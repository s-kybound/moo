open Syntax
(* a cocontextual typechecker that analyses a given program *)

type tycheck_var =
  { original_name : Ast.name
  ; unique_id : int
  }

type tycheck_binder =
  { original_binder : Ast.binder
  ; unique_ids : int list
  }

type tycheck_pattern_binder =
  | PatVar of tycheck_binder
  | PatWild of { unique_ids : int list }

type tycheck_pattern =
  | TPatVariable of tycheck_pattern_binder
  | TTup of tycheck_pattern_binder list
  | TConstr of
      { tpat_name : Ast.name
      ; tpat_args : tycheck_pattern_binder list
      }

type tycheck_term =
  | TMu of tycheck_binder * tycheck_command
  | TVariable of tycheck_var
  | TConstruction of
      { tcons_name : Ast.name
      ; tcons_args : tycheck_term list
      }
  | TTuple of tycheck_term list
  | TMatcher of (tycheck_pattern * tycheck_command) list
  | TNum of int64
  | TRec of tycheck_binder * tycheck_term
  | TArr of tycheck_term list
  | TAnn of tycheck_term * Ast.ty_use
  | TDone

and tycheck_command =
  | TCore of
      { tl_term : tycheck_term
      ; tr_term : tycheck_term
      }
  | TArith of tycheck_arith_command
  | TFork of tycheck_command * tycheck_command

and tycheck_arith_command =
  | TUnop of
      { top : Ast.unop
      ; tin_term : tycheck_term
      ; tout_term : tycheck_term
      }
  | TBop of
      { top : Ast.bop
      ; tl_term : tycheck_term
      ; tr_term : tycheck_term
      ; tout_term : tycheck_term
      }

and tycheck_definition =
  | TTermDef of tycheck_binder * tycheck_term
  | TTypeDef of Ast.kind_binder * Ast.ty
  | TModuleDef of tycheck_module_def

and tycheck_module_def =
  { tmod_name : string
  ; tprogram : tycheck_module
  }

and tycheck_module =
  { opens : Ast.module_open list
  ; definitions : tycheck_definition list
  ; command : tycheck_command option
  }

type context = (tycheck_var * Syntax.Ast.ty_use) list

let gen_int =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    counter := id + 1;
    id
;;

type tycheck_hole_environment_frame =
  | Top
  | Frame of
      { parent : tycheck_hole_environment_frame
      ; hole_var : Ast.binder
      ; mutable usages : int list
      }

let extend_hole_frame (parent : tycheck_hole_environment_frame) (hole_var : Ast.binder)
  : tycheck_hole_environment_frame
  =
  Frame { parent; hole_var; usages = [] }
;;

let extend_pattern_frame (parent : tycheck_hole_environment_frame) (pat : Ast.pattern)
  : tycheck_hole_environment_frame
  =
  match pat with
  | Ast.Pat_binder (Ast.Var binder) -> extend_hole_frame parent binder
  | Ast.Pat_binder Ast.Wildcard -> parent
  | Ast.Tup pat_binders ->
    List.fold_left
      (fun env_acc pat_binder ->
         match pat_binder with
         | Ast.Var binder -> extend_hole_frame env_acc binder
         | Ast.Wildcard -> env_acc)
      parent
      pat_binders
  | Ast.Constr { pat_name = _; pat_args } ->
    List.fold_left
      (fun env_acc pat_binder ->
         match pat_binder with
         | Ast.Var binder -> extend_hole_frame env_acc binder
         | Ast.Wildcard -> env_acc)
      parent
      pat_args
;;

let add_usage_to_hole
      (frame : tycheck_hole_environment_frame)
      (name : Ast.name)
      (usage_id : int)
  : unit
  =
  match name with
  | Base var ->
    let rec aux frame =
      match frame with
      | Top -> failwith "add_usage_to_hole: hole variable not found"
      | Frame f ->
        if f.hole_var.name = var then f.usages <- usage_id :: f.usages else aux f.parent
    in
    aux frame
  | Namespaced _ ->
    failwith "add_usage_to_hole: namespaced variables not supported for holes"
;;

let get_usages_of_hole (frame : tycheck_hole_environment_frame) (var : Ast.binder)
  : int list
  =
  let rec aux frame =
    match frame with
    | Top -> failwith "get_usages_of_hole: hole variable not found"
    | Frame f -> if f.hole_var = var then f.usages else aux f.parent
  in
  aux frame
;;

(* perform a co-debrujin conversion on a module *)
let tycheck_module_of_ast (modu : Syntax.Ast.module_) : tycheck_module =
  let rec tycheck_module_of_ast_aux (modu : Syntax.Ast.module_) env : tycheck_module =
    let rec tycheck_definition_of_ast (def : Syntax.Ast.definition) env
      : tycheck_definition
      =
      match def with
      | Syntax.Ast.TermDef (binder, term) ->
        let new_env = extend_hole_frame env binder in
        let tterm = tycheck_term_of_ast term new_env in
        let unique_ids = get_usages_of_hole new_env binder in
        let tbinder = { original_binder = binder; unique_ids } in
        TTermDef (tbinder, tterm)
      | Syntax.Ast.TypeDef (kind_binder, ty) -> TTypeDef (kind_binder, ty)
      | Syntax.Ast.ModuleDef { name; program } ->
        let tprogram = tycheck_module_of_ast_aux program env in
        TModuleDef { tmod_name = name; tprogram }
    and tycheck_term_of_ast (term : Syntax.Ast.term) env : tycheck_term =
      match term with
      | Syntax.Ast.Mu (binder, command) ->
        let new_env = extend_hole_frame env binder in
        let tcommand = tycheck_command_of_ast command new_env in
        let unique_ids = get_usages_of_hole new_env binder in
        let tbinder = { original_binder = binder; unique_ids } in
        TMu (tbinder, tcommand)
      | Syntax.Ast.Variable original_name ->
        let unique_id = gen_int () in
        let tvar = { original_name; unique_id } in
        add_usage_to_hole env original_name unique_id;
        TVariable tvar
      | Syntax.Ast.Construction { cons_name; cons_args } ->
        let tcons_args = List.map (fun arg -> tycheck_term_of_ast arg env) cons_args in
        TConstruction { tcons_name = cons_name; tcons_args }
      | Syntax.Ast.Tuple terms ->
        let tterms = List.map (fun term -> tycheck_term_of_ast term env) terms in
        TTuple tterms
      | Syntax.Ast.Matcher branches ->
        let tbranches =
          List.map
            (fun (pat, cmd) ->
               (*
                TODO: the workflow:
                1. generate a new environment from the pattern
                2. typecheck the command in that environment
                3. generate a new pattern given that new_env
              *)
               let new_env = extend_pattern_frame env pat in
               let tcmd = tycheck_command_of_ast cmd new_env in
               let tpat = tycheck_pattern_of_ast pat new_env in
               tpat, tcmd)
            branches
        in
        TMatcher tbranches
      | Syntax.Ast.Num n -> TNum n
      | Syntax.Ast.Rec (binder, term) ->
        let new_env = extend_hole_frame env binder in
        let tterm = tycheck_term_of_ast term new_env in
        let unique_ids = get_usages_of_hole new_env binder in
        let tbinder = { original_binder = binder; unique_ids } in
        TRec (tbinder, tterm)
      | Syntax.Ast.Arr terms ->
        let tterms = List.map (fun term -> tycheck_term_of_ast term env) terms in
        TArr tterms
      | Syntax.Ast.Ann (term, ty_use) ->
        let tterm = tycheck_term_of_ast term env in
        TAnn (tterm, ty_use)
      | Syntax.Ast.Done -> TDone
    and tycheck_command_of_ast (command : Syntax.Ast.command) env : tycheck_command =
      match command with
      | Syntax.Ast.Core { l_term; r_term } ->
        let tl_term = tycheck_term_of_ast l_term env in
        let tr_term = tycheck_term_of_ast r_term env in
        TCore { tl_term; tr_term }
      | Syntax.Ast.Arith arith_cmd ->
        (match arith_cmd with
         | Syntax.Ast.Unop { op; in_term; out_term } ->
           let tin_term = tycheck_term_of_ast in_term env in
           let tout_term = tycheck_term_of_ast out_term env in
           TArith (TUnop { top = op; tin_term; tout_term })
         | Syntax.Ast.Bop { op; l_term; r_term; out_term } ->
           let tl_term = tycheck_term_of_ast l_term env in
           let tr_term = tycheck_term_of_ast r_term env in
           let tout_term = tycheck_term_of_ast out_term env in
           TArith (TBop { top = op; tl_term; tr_term; tout_term }))
      | Syntax.Ast.Fork (cmd1, cmd2) ->
        let tcmd1 = tycheck_command_of_ast cmd1 env in
        let tcmd2 = tycheck_command_of_ast cmd2 env in
        TFork (tcmd1, tcmd2)
    and tycheck_pattern_of_ast (pat : Syntax.Ast.pattern) env : tycheck_pattern =
      match pat with
      | Syntax.Ast.Pat_binder (Var binder) ->
        let unique_ids = get_usages_of_hole env binder in
        let tpat_binder = { original_binder = binder; unique_ids } in
        TPatVariable (PatVar tpat_binder)
      | Syntax.Ast.Pat_binder Wildcard ->
        let unique_ids = [] in
        let tpat_binder = PatWild { unique_ids } in
        TPatVariable tpat_binder
      | Syntax.Ast.Tup pat_binders ->
        let tpat_binders =
          List.map
            (fun pat_binder ->
               match pat_binder with
               | Syntax.Ast.Var binder ->
                 let unique_ids = get_usages_of_hole env binder in
                 let tpat_binder = { original_binder = binder; unique_ids } in
                 PatVar tpat_binder
               | Syntax.Ast.Wildcard ->
                 let unique_ids = [] in
                 PatWild { unique_ids })
            pat_binders
        in
        TTup tpat_binders
      | Syntax.Ast.Constr { pat_name; pat_args } ->
        let tpat_args =
          List.map
            (fun pat_binder ->
               match pat_binder with
               | Syntax.Ast.Var binder ->
                 let unique_ids = get_usages_of_hole env binder in
                 let tpat_binder = { original_binder = binder; unique_ids } in
                 PatVar tpat_binder
               | Syntax.Ast.Wildcard ->
                 let unique_ids = [] in
                 PatWild { unique_ids })
            pat_args
        in
        TConstr { tpat_name = pat_name; tpat_args }
    in
    let new_definitions, new_env =
      List.fold_left
        (fun (defs_acc, env_acc) def ->
           let tdef = tycheck_definition_of_ast def env_acc in
           defs_acc @ [ tdef ], env_acc)
        ([], env)
        modu.definitions
    in
    { opens = modu.opens
    ; definitions = new_definitions
    ; command = Option.map (fun cmd -> tycheck_command_of_ast cmd new_env) modu.command
    }
  in
  tycheck_module_of_ast_aux modu Top
;;

let rec tycheck_module_to_ast (tmodu : tycheck_module) : Syntax.Ast.module_ =
  let rec tycheck_definition_to_ast (tdef : tycheck_definition) : Syntax.Ast.definition =
    match tdef with
    | TTermDef (tbinder, tterm) ->
      let ast_binder = tbinder.original_binder in
      let ast_term = tycheck_term_to_ast tterm in
      Syntax.Ast.TermDef (ast_binder, ast_term)
    | TTypeDef (kind_binder, ty) -> Syntax.Ast.TypeDef (kind_binder, ty)
    | TModuleDef { tmod_name; tprogram } ->
      let program = tycheck_module_to_ast tprogram in
      Syntax.Ast.ModuleDef { name = tmod_name; program }
  and tycheck_term_to_ast (tterm : tycheck_term) : Syntax.Ast.term =
    match tterm with
    | TMu (tbinder, tcommand) ->
      let ast_binder = tbinder.original_binder in
      let ast_command = tycheck_command_to_ast tcommand in
      Syntax.Ast.Mu (ast_binder, ast_command)
    | TVariable tvar ->
      let ast_name = tvar.original_name in
      Syntax.Ast.Variable ast_name
    | TConstruction { tcons_name; tcons_args } ->
      let ast_args = List.map tycheck_term_to_ast tcons_args in
      Syntax.Ast.Construction { cons_name = tcons_name; cons_args = ast_args }
    | TTuple tterms ->
      let ast_terms = List.map tycheck_term_to_ast tterms in
      Syntax.Ast.Tuple ast_terms
    | TMatcher tbranches ->
      let ast_branches =
        List.map
          (fun (tpat, tcmd) ->
             let ast_pat = tycheck_pattern_to_ast tpat in
             let ast_cmd = tycheck_command_to_ast tcmd in
             ast_pat, ast_cmd)
          tbranches
      in
      Syntax.Ast.Matcher ast_branches
    | TNum n -> Syntax.Ast.Num n
    | TRec (tbinder, tterm) ->
      let ast_binder = tbinder.original_binder in
      let ast_term = tycheck_term_to_ast tterm in
      Syntax.Ast.Rec (ast_binder, ast_term)
    | TArr tterms ->
      let ast_terms = List.map tycheck_term_to_ast tterms in
      Syntax.Ast.Arr ast_terms
    | TAnn (tterm, ty_use) ->
      let ast_term = tycheck_term_to_ast tterm in
      Syntax.Ast.Ann (ast_term, ty_use)
    | TDone -> Syntax.Ast.Done
  and tycheck_command_to_ast (tcommand : tycheck_command) : Syntax.Ast.command =
    match tcommand with
    | TCore { tl_term; tr_term } ->
      let l_term = tycheck_term_to_ast tl_term in
      let r_term = tycheck_term_to_ast tr_term in
      Syntax.Ast.Core { l_term; r_term }
    | TArith (TUnop { top; tin_term; tout_term }) ->
      let in_term = tycheck_term_to_ast tin_term in
      let out_term = tycheck_term_to_ast tout_term in
      Syntax.Ast.Arith (Syntax.Ast.Unop { op = top; in_term; out_term })
    | TArith (TBop { top; tl_term; tr_term; tout_term }) ->
      let l_term = tycheck_term_to_ast tl_term in
      let r_term = tycheck_term_to_ast tr_term in
      let out_term = tycheck_term_to_ast tout_term in
      Syntax.Ast.Arith (Syntax.Ast.Bop { op = top; l_term; r_term; out_term })
    | TFork (tcmd1, tcmd2) ->
      let cmd1 = tycheck_command_to_ast tcmd1 in
      let cmd2 = tycheck_command_to_ast tcmd2 in
      Syntax.Ast.Fork (cmd1, cmd2)
  and tycheck_patbinder_to_ast (tpat_binder : tycheck_pattern_binder)
    : Syntax.Ast.pattern_binder
    =
    match tpat_binder with
    | PatVar tbinder ->
      let ast_binder = tbinder.original_binder in
      Syntax.Ast.Var ast_binder
    | PatWild _ -> Syntax.Ast.Wildcard
  and tycheck_pattern_to_ast (tpat : tycheck_pattern) : Syntax.Ast.pattern =
    match tpat with
    | TPatVariable (PatVar binder) ->
      let ast_pat_binder = binder.original_binder in
      Syntax.Ast.Pat_binder (Var ast_pat_binder)
    | TPatVariable (PatWild _) -> Syntax.Ast.Pat_binder Wildcard
    | TTup tpat_binders ->
      let ast_pat_binders = List.map tycheck_patbinder_to_ast tpat_binders in
      Syntax.Ast.Tup ast_pat_binders
    | TConstr { tpat_name; tpat_args } ->
      let ast_pat_args = List.map tycheck_patbinder_to_ast tpat_args in
      Syntax.Ast.Constr { pat_name = tpat_name; pat_args = ast_pat_args }
  in
  { opens = tmodu.opens
  ; definitions = List.map tycheck_definition_to_ast tmodu.definitions
  ; command = Option.map tycheck_command_to_ast tmodu.command
  }
;;

let rec synthesize (checkables : context) (expr : string) : Syntax.Ast.ty_use * context =
  (* Placeholder implementation for synthesis *)
  raise (Failure "synthesize not implemented")

and check (checkables : context) (expr : string) (expected_type : Syntax.Ast.ty_use)
  : context
  =
  (* Placeholder implementation for checking *)
  checkables
;;
