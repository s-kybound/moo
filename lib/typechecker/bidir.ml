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

and tycheck_top_level_item =
  | Open of Ast.module_open
  | Def of tycheck_definition

and tycheck_module = tycheck_top_level_item list * tycheck_command option

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
  let rec tycheck_module_of_ast_aux
            ((top_level_defs, top_level_command) : Syntax.Ast.module_)
            env
    : tycheck_module
    =
    let rec tycheck_definition_of_ast (def : Syntax.Ast.definition) env
      : tycheck_definition * tycheck_hole_environment_frame
      =
      match def with
      | Syntax.Ast.TermDef (binder, term) ->
        let new_env = extend_hole_frame env binder in
        let tterm = tycheck_term_of_ast term new_env in
        (* too early to do below. we need to do a second pass after the lower definitions and commands have been
         * evaluated*)
        (* let unique_ids = get_usages_of_hole new_env binder in *)
        let tbinder = { original_binder = binder; unique_ids = [] } in
        TTermDef (tbinder, tterm), new_env
      | Syntax.Ast.TypeDef (kind_binder, ty) -> TTypeDef (kind_binder, ty), env
      | Syntax.Ast.ModuleDef { name; program } ->
        let tprogram = tycheck_module_of_ast_aux program env in
        TModuleDef { tmod_name = name; tprogram }, env
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
        if List.is_empty unique_ids
        then (
          let msg =
            Printf.sprintf
              "tycheck_term_of_ast: recursive binder %s has no usages"
              (Syntax.Pretty.show_binder binder)
          in
          failwith msg)
        else (
          let tbinder = { original_binder = binder; unique_ids } in
          TRec (tbinder, tterm))
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
    and tycheck_top_level_item_of_ast
          (tli : Syntax.Ast.definition Syntax.Ast.top_level_item)
          env
      : tycheck_top_level_item * tycheck_hole_environment_frame
      =
      match tli with
      | Syntax.Ast.Open o -> Open o, env
      | Syntax.Ast.Def d ->
        let tdef, new_env = tycheck_definition_of_ast d env in
        Def tdef, new_env
    in
    (* TODO *)
    let unannotated_definitions, new_env, env_checkpoints =
      List.fold_left
        (fun (defs_acc, env_acc, env_checkpoints) def ->
           let def, new_env = tycheck_top_level_item_of_ast def env_acc in
           defs_acc @ [ def ], new_env, env_checkpoints @ [ new_env ])
        ([], env, [])
        top_level_defs
    in
    let command =
      Option.map (fun cmd -> tycheck_command_of_ast cmd new_env) top_level_command
    in
    let top_level_items =
      List.map2
        (fun def env_checkpoint ->
           match def with
           | Def (TTermDef (tbinder, tterm)) ->
             let unique_ids = get_usages_of_hole env_checkpoint tbinder.original_binder in
             Def (TTermDef ({ tbinder with unique_ids }, tterm))
           | _ -> def)
        unannotated_definitions
        env_checkpoints
    in
    top_level_items, command
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
  and tycheck_top_level_item_to_ast tli : Syntax.Ast.definition Syntax.Ast.top_level_item =
    match tli with
    | Open o -> Open o
    | Def d -> Def (tycheck_definition_to_ast d)
  in
  let defs, maybe_cmd = tmodu in
  List.map tycheck_top_level_item_to_ast defs, Option.map tycheck_command_to_ast maybe_cmd
;;

let invert (ty_use : Syntax.Ast.ty_use) : Syntax.Ast.ty_use =
  match ty_use with
  | Polarised (Plus, mty) -> Polarised (Minus, mty)
  | Polarised (Minus, mty) -> Polarised (Plus, mty)
  | Abstract { negated; name } -> Abstract { negated = not negated; name }
  | Unresolved (Destructor raw_ty) -> Unresolved raw_ty
  | Unresolved raw_ty -> Unresolved (Destructor raw_ty)
  | Unmoded (Plus, ty) -> Unmoded (Minus, ty)
  | Unmoded (Minus, ty) -> Unmoded (Plus, ty)
;;

type context = (int * Syntax.Ast.ty_use) list

type tydef_env =
  | Top
  | TyFrame of
      { parent : tydef_env
      ; var : Ast.name
      ; ty : Syntax.Ast.ty
      }

let lookup (name : Ast.name) (tydef_env : tydef_env) : Syntax.Ast.ty =
  match name with
  | Base _ ->
    let rec aux env =
      match env with
      | Top -> failwith "lookup: type not found in environment"
      | TyFrame { parent; var = frame_var; ty } ->
        if frame_var = name then ty else aux parent
    in
    aux tydef_env
  | Namespaced _ -> failwith "lookup: namespaced types not supported"
;;

let rec tyu_equal (tyu1 : Syntax.Ast.ty_use) (tyu2 : Syntax.Ast.ty_use) tydef_env : bool =
  match tyu1, tyu2 with
  | Polarised (pol1, (mode1, ty1)), Polarised (pol2, (mode2, ty2)) ->
    pol1 = pol2 && mode1 = mode2 && ty_equal ty1 ty2 tydef_env
  | Abstract { negated = neg1; name = name1 }, Abstract { negated = neg2; name = name2 }
    -> neg1 = neg2 && name1 = name2
  | Abstract _, _ | _, Abstract _ ->
    failwith "TODO: abstract type equality not implemented in tyu_equal"
  | Unresolved raw_ty1, Unresolved raw_ty2 -> rty_equal raw_ty1 raw_ty2 tydef_env
  | Polarised (polarity, (_, ty)), Unresolved raw_ty
  | Unresolved raw_ty, Polarised (polarity, (_, ty)) ->
    (match ty with
     | Named (name, []) ->
       let rec nested_lookup name =
         match lookup name tydef_env with
         | Raw (chirality, raw_ty) ->
           (match polarity, chirality with
            | Plus, Ast.Data | Minus, Ast.Codata -> raw_ty
            | Plus, Ast.Codata | Minus, Ast.Data -> Destructor raw_ty)
         | Named (inner_name, []) -> nested_lookup inner_name
         | Named (_, _rest) ->
           failwith "TODO: named type lookup in tyu_equal with parameters"
       in
       rty_equal raw_ty (nested_lookup name) tydef_env
     | Named (_, _rest) -> failwith "TODO: named type lookup in tyu_equal"
     | Raw (_, raw_ty2) -> rty_equal raw_ty raw_ty2 tydef_env)
  | _ -> failwith "TODO"

and ty_equal (ty1 : Syntax.Ast.ty) (ty2 : Syntax.Ast.ty) tydef_env : bool =
  match ty1, ty2 with
  | Named (name1, []), ty2 -> ty_equal (lookup name1 tydef_env) ty2 tydef_env
  | ty1, Named (name2, []) -> ty_equal ty1 (lookup name2 tydef_env) tydef_env
  | Named _, _ | _, Named _ ->
    failwith "TODO: named type equality with parameters not implemented in ty_equal"
  | Raw (shape1, raw_ty1), Raw (shape2, raw_ty2) ->
    shape1 = shape2 && rty_equal raw_ty1 raw_ty2 tydef_env

and rty_equal
      (rty1 : Syntax.Ast.raw_ty)
      (rty2 : Syntax.Ast.raw_ty)
      (tydef_env : tydef_env)
  : bool
  =
  match rty1, rty2 with
  | Raw64, Raw64 -> true
  | Product tys1, Product tys2 ->
    List.length tys1 = List.length tys2
    && List.for_all2
         (fun ty_use1 ty_use2 -> tyu_equal ty_use1 ty_use2 tydef_env)
         tys1
         tys2
  | Destructor raw_ty1, Destructor raw_ty2 -> rty_equal raw_ty1 raw_ty2 tydef_env
  | _, _ -> false
;;

(* Given a constructor and arity, look up the first matching type *)
let type_of_constructor
      (constr_name : Ast.name)
      (constr_arity : int)
      (tydef_env : tydef_env)
  : (Ast.name * Syntax.Ast.ty) option
  =
  (* placeholder implementation for constructor lookup *)
  let raw_constr_name = Ast.raw_of_name constr_name in
  let namespace_path = Ast.namespaced_path constr_name in
  let rec aux env =
    match env with
    | Top -> None
    | TyFrame { parent; var; ty = Raw (_, Variant variants) as ty } ->
      if Ast.namespaced_path var <> namespace_path
      then aux parent
      else (
        let is_matching_variant (v : Ast.variant) =
          v.constr_name = raw_constr_name && List.length v.constr_args = constr_arity
        in
        match List.find_opt is_matching_variant variants with
        | Some _ -> Some (var, ty)
        | None -> aux parent)
    | TyFrame { parent; _ } -> aux parent
  in
  aux tydef_env
;;

(* given a constructor and a type, get the types of the constructor's arguments 
 * invariant: type must match*)
let args_of_variant (constr : Ast.name) (ty : Ast.ty) : Syntax.Ast.ty_use list =
  let raw_constr = Ast.raw_of_name constr in
  match ty with
  | Raw (_, Variant variants) ->
    (match
       List.find_opt (fun (v : Ast.variant) -> v.constr_name = raw_constr) variants
     with
     | Some v -> v.constr_args
     | None -> assert false)
  | _ -> assert false
;;

exception TypeMismatch of Ast.ty_use * Ast.ty_use * string
exception TypeError of string
exception Underspecified of string

let get_raw_type (ty_use : Syntax.Ast.ty_use) (tydef_env : tydef_env) : Syntax.Ast.raw_ty =
  match ty_use with
  | Syntax.Ast.Unresolved raw_ty -> raw_ty
  | Syntax.Ast.Abstract _ -> failwith "get_raw_type: cannot get raw type of abstract type"
  | Syntax.Ast.Polarised (_, (_, ty)) | Syntax.Ast.Unmoded (_, ty) ->
    (match ty with
     | Named (name, []) ->
       let rec nested_lookup name =
         match lookup name tydef_env with
         | Raw (_, raw_ty) -> raw_ty
         | Named (inner_name, []) -> nested_lookup inner_name
         | Named (_, _rest) ->
           failwith "TODO: named type lookup in get_raw_type with parameters"
       in
       nested_lookup name
     | Named (_, _rest) -> failwith "TODO: named type lookup in get_raw_type"
     | Raw (_, raw_ty) -> raw_ty)
;;

(* Workflow - synthesize takes in a set of invariants, and determines the type of an expression.
 *            it returns the demands in order to have that expression have that type *)
let rec synthesize (checkables : context) (expr : tycheck_term) (tydef_env : tydef_env)
  : Syntax.Ast.ty_use * context
  =
  match expr with
  | TVariable tvar ->
    (match List.assoc_opt tvar.unique_id (List.map (fun (v, ty) -> v, ty) checkables) with
     | Some ty_use -> ty_use, []
     | None ->
       let msg =
         Printf.sprintf
           "synthesize: variable %s not found in context"
           (Syntax.Pretty.show_name tvar.original_name)
       in
       raise (Underspecified msg))
  | TNum _ -> Ast.Unresolved Raw64, []
  | TDone -> Ast.Unresolved (Destructor (Product [])), []
  | TTuple [] -> Ast.Unresolved (Product []), []
  | TTuple terms ->
    let terms, total_demands =
      List.fold_left
        (fun (tys_acc, ctx_acc) term ->
           let ty_use, term_ctx = synthesize checkables term tydef_env in
           tys_acc @ [ ty_use ], ctx_acc @ term_ctx)
        ([], [])
        terms
    in
    Ast.Unresolved (Product terms), total_demands
  | TAnn (tterm, ty_use) ->
    let demands = check checkables tterm ty_use tydef_env in
    ty_use, demands
  | TRec (_tbinder, tterm) ->
    (* placeholder implementation for rec *)
    let inferred_ty, demands = synthesize checkables tterm tydef_env in
    inferred_ty, demands
  | TMu (tbinder, tcommand) ->
    let demands = typecheck_command checkables tcommand tydef_env in
    (* lookup the type of the tbinder in the demands *)
    let relevant_ids = tbinder.unique_ids in
    (* collect the demands with the relevant ids *)
    let relevant_demands =
      List.filter (fun (id, _ty_use) -> List.mem id relevant_ids) demands
    in
    (match relevant_demands with
     | [] -> raise (Underspecified "synthesize: no demands found for mu binder")
     | first :: rest ->
       (* ensure that the demands are the same *)
       let inferred_ty = snd first in
       let rec verify_demands demands =
         match demands with
         | [] -> ()
         | (_var, ty_use) :: tail ->
           if not (tyu_equal ty_use inferred_ty tydef_env)
           then
             raise
               (TypeMismatch
                  (inferred_ty, ty_use, "synthesize: conflicting demands for mu binder"))
           else verify_demands tail
       in
       verify_demands rest;
       invert inferred_ty, demands)
  | TMatcher branches ->
    let most_specific_type, demands =
      List.fold_left
        (fun (_most_specific_type, _demands) (_pattern, _command) ->
           failwith "TODO: TMatcher")
        (None, [])
        branches
    in
    (match most_specific_type with
     | None -> assert false
     | Some tyu -> tyu, demands)
  | TConstruction { tcons_name; tcons_args } ->
    let typ = type_of_constructor tcons_name (List.length tcons_args) tydef_env in
    (match typ with
     | None ->
       let msg =
         Printf.sprintf
           "synthesize: type for variant %s with arity %d not found"
           (Syntax.Pretty.show_name tcons_name)
           (List.length tcons_args)
       in
       raise (TypeError msg)
     | Some (_ty_name, ty) ->
       let constructor_tyu_of_ty _ty =
         failwith "TODO: constructor_tyu_of_ty not implemented"
       in
       let ty_use = constructor_tyu_of_ty ty in
       ty_use, check checkables expr ty_use tydef_env)
  | TArr terms ->
    (* ensure that each term is ty_equal with the last, and return the most
     * specific term *)
    let most_specific_term, total_demands =
      List.fold_left
        (fun (ty_acc, ctx_acc) term ->
           let ty_use, term_ctx = synthesize checkables term tydef_env in
           match ty_acc with
           | None -> Some ty_use, ctx_acc @ term_ctx
           | Some ty_use_acc ->
             if not (tyu_equal ty_use_acc ty_use tydef_env)
             then
               raise
                 (TypeMismatch
                    (ty_use_acc, ty_use, "synthesize: TArr terms have mismatched types"))
             else ty_acc, ctx_acc @ term_ctx)
        (None, [])
        terms
    in
    (match most_specific_term with
     | None ->
       (* Ast.Unresolved (Array Ast.Weak), []*) failwith "synthesize: TArr with no terms"
     | Some most_specific_term -> Ast.Unresolved (Array most_specific_term), total_demands)

(* workflow - given demands, check an expression with a type and output discoveries *)

and check
      (checkables : context)
      (expr : tycheck_term)
      (expected_type : Syntax.Ast.ty_use)
      (tydef_env : tydef_env)
  : context
  =
  let raw_ty = get_raw_type expected_type tydef_env in
  match expr with
  | TVariable tvar -> [ tvar.unique_id, expected_type ]
  | TNum _ ->
    if tyu_equal expected_type (Ast.Unresolved Raw64) tydef_env
    then []
    else
      raise
        (TypeMismatch
           (expected_type, Ast.Unresolved Raw64, "check: TNum expected type mismatch"))
  | TDone ->
    if tyu_equal expected_type (Ast.Unresolved (Destructor (Product []))) tydef_env
    then []
    else
      raise
        (TypeMismatch
           ( expected_type
           , Ast.Unresolved (Destructor Raw64)
           , "check: TDone expected type mismatch" ))
  | TMu (tbinder, tcommand) ->
    let tbinder_ty = invert expected_type in
    let new_demands = List.map (fun id -> id, tbinder_ty) tbinder.unique_ids in
    let updated_checkables = checkables @ new_demands in
    typecheck_command updated_checkables tcommand tydef_env
  | TTuple [] ->
    if tyu_equal expected_type (Ast.Unresolved (Product [])) tydef_env
    then []
    else
      raise
        (TypeMismatch
           ( expected_type
           , Ast.Unresolved (Product [])
           , "check: TTuple [] expected type mismatch" ))
  | TTuple terms ->
    (match raw_ty with
     | Product expected_tys ->
       if List.length terms <> List.length expected_tys
       then
         raise
           (TypeMismatch
              ( expected_type
              , Ast.Unresolved (Product expected_tys)
              , "check: TTuple arity mismatch" ))
       else
         List.fold_left2
           (fun ctx_acc term expected_ty ->
              let term_demands = check checkables term expected_ty tydef_env in
              ctx_acc @ term_demands)
           []
           terms
           expected_tys
     | _ ->
       raise
         (TypeMismatch
            ( expected_type
            , Ast.Unresolved (Product [])
            , "check: TTuple expected type mismatch" )))
  | TAnn (tterm, ty_use) ->
    if tyu_equal ty_use expected_type tydef_env
    then check checkables tterm ty_use tydef_env
    else raise (TypeMismatch (expected_type, ty_use, "check: TAnn type mismatch"))
  | TRec (tbinder, tterm) ->
    let new_demands = List.map (fun id -> id, expected_type) tbinder.unique_ids in
    let updated_checkables = checkables @ new_demands in
    check updated_checkables tterm expected_type tydef_env
  | TMatcher _ ->
    (* placeholder implementation for matcher *)
    failwith "check: matcher not implemented"
  | TConstruction { tcons_name = _; tcons_args = _ } ->
    let ty_use, discoveries = synthesize checkables expr tydef_env in
    if tyu_equal expected_type ty_use tydef_env
    then discoveries
    else
      raise (TypeMismatch (expected_type, ty_use, "check: TConstruction type mismatch"))
  | TArr [] ->
    (match get_raw_type expected_type tydef_env with
     | Array _ -> []
     | _ ->
       raise
         (TypeMismatch
            ( expected_type
            , Ast.Unresolved (Array (Ast.Unresolved Raw64)) (* TODO: Raw64 -> Weak *)
            , "check: TArr [] expected type mismatch" )))
  | TArr _terms ->
    (* placeholder implementation for arrays *)
    failwith "check: arrays not implemented"

and typecheck_command
      (checkables : context)
      (command : tycheck_command)
      (tydef_env : tydef_env)
  : context
  =
  match command with
  | TCore { tl_term; tr_term } ->
    (try
       let l_ty_use, l_demands = synthesize checkables tl_term tydef_env in
       let r_ty_use = invert l_ty_use in
       let r_demands = check checkables tr_term r_ty_use tydef_env in
       l_demands @ r_demands
     with
     | Underspecified msg ->
       let warning_msg =
         Printf.sprintf
           "typecheck_command: underspecified left term, trying right term. %s"
           msg
       in
       print_endline warning_msg;
       let r_ty_use, r_demands = synthesize checkables tr_term tydef_env in
       let l_ty_use = invert r_ty_use in
       let l_demands = check checkables tl_term l_ty_use tydef_env in
       l_demands @ r_demands
     | TypeMismatch (expected, actual, msg) ->
       let msg =
         Printf.sprintf
           "Type mismatch in TCore: expected %s but got %s. %s"
           (Syntax.Pretty.show_ty_use expected)
           (Syntax.Pretty.show_ty_use actual)
           msg
       in
       failwith msg
     | e -> raise e)
  | TArith (TBop { top = _; tl_term; tr_term; tout_term }) ->
    let out_ty_use, out_demands = synthesize checkables tout_term tydef_env in
    let in_ty_use = invert out_ty_use in
    if not (tyu_equal out_ty_use (Ast.Unresolved (Destructor Raw64)) tydef_env)
    then
      raise
        (TypeMismatch
           ( Ast.Unresolved (Destructor Raw64)
           , out_ty_use
           , "typecheck_command: arithmetic binary operation expected raw64 output" ))
    else (
      let left_demands = check checkables tl_term in_ty_use tydef_env in
      let right_demands = check checkables tr_term in_ty_use tydef_env in
      out_demands @ left_demands @ right_demands)
  | TArith (TUnop { top = _; tin_term; tout_term }) ->
    let out_ty_use, out_demands = synthesize checkables tout_term tydef_env in
    let in_ty_use = invert out_ty_use in
    if not (tyu_equal out_ty_use (Ast.Unresolved (Destructor Raw64)) tydef_env)
    then
      raise
        (TypeMismatch
           ( Ast.Unresolved (Destructor Raw64)
           , out_ty_use
           , "typecheck_command: arithmetic unary operation expected raw64 output" ))
    else (
      let in_demands = check checkables tin_term in_ty_use tydef_env in
      out_demands @ in_demands)
  | TFork (cmd1, cmd2) ->
    let ctx1 = typecheck_command checkables cmd1 tydef_env in
    let ctx2 = typecheck_command checkables cmd2 tydef_env in
    ctx1 @ ctx2
;;

let rec tycheck_definition
          (checkables : context)
          (def : tycheck_definition)
          (tydef_env : tydef_env)
  : context * tydef_env
  =
  match def with
  | TTermDef (tbinder, tterm) ->
    (match tbinder.original_binder.typ with
     | None ->
       let inferred_ty, demands = synthesize checkables tterm tydef_env in
       let new_demands = List.map (fun id -> id, inferred_ty) tbinder.unique_ids in
       let total_demands = demands @ new_demands in
       total_demands, tydef_env
     | Some ty_use ->
       let insights = check checkables tterm ty_use tydef_env in
       let new_insights = List.map (fun id -> id, ty_use) tbinder.unique_ids in
       let total_insights = insights @ new_insights in
       total_insights, tydef_env)
  | TTypeDef ((name, _typs), ty) ->
    let new_tydef_env = TyFrame { parent = tydef_env; var = Base name; ty } in
    [], new_tydef_env
  | TModuleDef { tmod_name = _; tprogram } ->
    let new_insights, _ = tycheck_module checkables tprogram tydef_env in
    new_insights, tydef_env

and tycheck_module
      (checkables : context)
      ((top_level_items, top_level_command) : tycheck_module)
      (tydef_env : tydef_env)
  : context * tydef_env
  =
  let rec process_top_level_items
            (defs : tycheck_top_level_item list)
            (checkables_acc : context)
            (tydef_env_acc : tydef_env)
    : context * tydef_env
    =
    match defs with
    | [] -> checkables_acc, tydef_env_acc
    | Def def :: rest ->
      let new_insights, new_tydef_env =
        tycheck_definition checkables_acc def tydef_env_acc
      in
      let updated_checkables = checkables_acc @ new_insights in
      process_top_level_items rest updated_checkables new_tydef_env
    | Open _ :: rest -> process_top_level_items rest checkables_acc tydef_env_acc
  in
  let after_defs_checkables, after_defs_tydef_env =
    process_top_level_items top_level_items checkables tydef_env
  in
  match top_level_command with
  | None -> after_defs_checkables, after_defs_tydef_env
  | Some command ->
    let command_insights =
      typecheck_command after_defs_checkables command after_defs_tydef_env
    in
    let total_insights = after_defs_checkables @ command_insights in
    total_insights, after_defs_tydef_env
;;

let tycheck_program (modu : Ast.module_) : unit =
  let modu = tycheck_module_of_ast modu in
  tycheck_module [] modu Top |> ignore
;;
