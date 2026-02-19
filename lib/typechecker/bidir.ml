open Syntax
open Type
(* a cocontextual typechecker that analyses a given program *)

type tycheck_var =
  { original_name : Ast.name
  ; unique_id : int
  }

type tycheck_binder =
  { original_binder : Ast.binder
  ; unique_ids : int list
  }

type tycheck_pattern =
  | TPatVariable of tycheck_binder
  | TTup of tycheck_binder list
  | TConstr of
      { tpat_name : Ast.name
      ; tpat_args : tycheck_binder list
      }
  | TNumeral of int64

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
      ; hole_var : string
      ; mutable usages : int list
      }

let extend_hole_frame (parent : tycheck_hole_environment_frame) (hole_var : Ast.binder)
  : tycheck_hole_environment_frame
  =
  match hole_var with
  | Ast.Var var -> Frame { parent; hole_var = var; usages = [] }
  | Ast.Wildcard -> parent
;;

let extend_pattern_frame (parent : tycheck_hole_environment_frame) (pat : Ast.pattern)
  : tycheck_hole_environment_frame
  =
  match pat with
  | Ast.Binder binder -> extend_hole_frame parent binder
  | Ast.Tup pat_binders ->
    List.fold_left
      (fun env_acc pat_binder -> extend_hole_frame env_acc pat_binder)
      parent
      pat_binders
  | Ast.Constr { pat_name = _; pat_args } ->
    List.fold_left
      (fun env_acc pat_binder -> extend_hole_frame env_acc pat_binder)
      parent
      pat_args
  | Ast.Numeral _ -> parent
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
        if f.hole_var = var then f.usages <- usage_id :: f.usages else aux f.parent
    in
    aux frame
  | Namespaced _ ->
    failwith "add_usage_to_hole: namespaced variables not supported for holes"
;;

let get_usages_of_hole (frame : tycheck_hole_environment_frame) (var : Ast.binder)
  : int list
  =
  match var with
  | Ast.Wildcard -> []
  | Ast.Var var ->
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
      | Syntax.Ast.Numeral n -> TNumeral n
      | Syntax.Ast.Binder binder ->
        let unique_ids = get_usages_of_hole env binder in
        let tpat_binder = { original_binder = binder; unique_ids } in
        TPatVariable tpat_binder
      | Syntax.Ast.Tup pat_binders ->
        let tpat_binders =
          List.map
            (fun pat_binder ->
               let unique_ids = get_usages_of_hole env pat_binder in
               { original_binder = pat_binder; unique_ids })
            pat_binders
        in
        TTup tpat_binders
      | Syntax.Ast.Constr { pat_name; pat_args } ->
        let tpat_args =
          List.map
            (fun pat_binder ->
               let unique_ids = get_usages_of_hole env pat_binder in
               { original_binder = pat_binder; unique_ids })
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

module IMap = Map.Make (Int)

type context = Ast.ty_use IMap.t

let merge_contexts (ctx1 : context) (ctx2 : context) tydef_env : context =
  IMap.union
    (fun _ tyu1 tyu2 -> Some (Type.most_specific_tyu tyu1 tyu2 tydef_env))
    ctx1
    ctx2
;;

let type_of_usages (ids : int list) (ctx : context) (tydef_env : tydef_env)
  : (Ast.ty_use option, string) result
  =
  List.fold_left
    (fun acc id ->
       match acc, IMap.find_opt id ctx with
       | Error _, _ -> acc
       | Ok None, result | Ok result, None -> Ok result
       | Ok (Some tyu), Some tyu' ->
         if tyu_equal tyu tyu' tydef_env
         then Ok (Some (Type.most_specific_tyu tyu tyu' tydef_env))
         else (
           let msg =
             Printf.sprintf
               "type_of_usages: conflicting types for id %d: %s vs %s"
               id
               (Syntax.Pretty.show_ty_use tyu)
               (Syntax.Pretty.show_ty_use tyu')
           in
           Error msg))
    (Ok None)
    ids
;;

exception TypeMismatch of Ast.ty_use * Ast.ty_use * string
exception TypeError of string
exception Underspecified of string

let annotate term tyu = TAnn (term, tyu)

(* Workflow - synthesize takes in a set of invariants, and determines the type of an expression.
 *            it returns the demands in order to have that expression have that type 
 *            it also returns the annotated terms themselves *)
let rec synthesize (knowledge : context) (expr : tycheck_term) (tydef_env : tydef_env)
  : tycheck_term * Syntax.Ast.ty_use * context
  =
  let annotate_with = annotate expr in
  match expr with
  | TVariable tvar ->
    (match IMap.find_opt tvar.unique_id knowledge with
     | Some ty_use -> annotate_with ty_use, ty_use, knowledge
     | None ->
       let msg =
         Printf.sprintf
           "synthesize: variable %s not found in context"
           (Syntax.Pretty.show_name tvar.original_name)
       in
       raise (Underspecified msg))
  | TNum _ ->
    let tyu = Type.new_constructor_tyu Raw64 in
    annotate_with tyu, tyu, knowledge
  | TDone ->
    let tyu = Type.negate_tyu (Type.new_constructor_tyu (Product [])) in
    annotate_with tyu, tyu, knowledge
  | TTuple [] ->
    let tyu = Type.new_constructor_tyu (Product []) in
    annotate_with tyu, tyu, knowledge
  | TTuple terms ->
    let terms, typs, new_knowledge =
      List.fold_left
        (fun (terms_acc, tys_acc, ctx_acc) term ->
           let term, ty_use, term_ctx = synthesize ctx_acc term tydef_env in
           ( terms_acc @ [ term ]
           , tys_acc @ [ ty_use ]
           , merge_contexts ctx_acc term_ctx tydef_env ))
        ([], [], knowledge)
        terms
    in
    let tyu = Type.new_constructor_tyu (Product typs) in
    annotate (TTuple terms) tyu, tyu, new_knowledge
  | TAnn (tterm, ty_use) ->
    let _, demands = check knowledge tterm ty_use tydef_env in
    expr, ty_use, demands
  | TRec (tbinder, tterm) ->
    let _, inferred_ty, demands = synthesize knowledge tterm tydef_env in
    let relevant_ids = tbinder.unique_ids in
    (match type_of_usages relevant_ids demands tydef_env with
     | Ok None -> raise (Underspecified "synthesize: no demands found for rec binder")
     | Error msg -> raise (TypeError msg)
     | Ok (Some ty_use) ->
       let tyu = most_specific_tyu inferred_ty ty_use tydef_env in
       annotate_with tyu, tyu, demands)
  | TMu (tbinder, tcommand) ->
    let tcommand, new_knowledge = typecheck_command knowledge tcommand tydef_env in
    (* lookup the type of the tbinder in the demands *)
    let relevant_ids = tbinder.unique_ids in
    (* collect the demands with the relevant ids *)
    (match type_of_usages relevant_ids new_knowledge tydef_env with
     | Ok None -> raise (Underspecified "synthesize: no demands found for mu binder")
     | Error msg -> raise (TypeError msg)
     | Ok (Some ty_use) ->
       let tyu = Type.negate_tyu ty_use in
       let expr = TMu (tbinder, tcommand) in
       annotate expr tyu, tyu, new_knowledge)
  | TMatcher branches ->
    let new_branches, most_specific_type, new_knowledge =
      List.fold_left
        (fun (branches_acc, most_specific_type, demands) (pattern, command) ->
           let new_command, tyu_of_pattern_opt, new_knowledge =
             match pattern with
             | TNumeral _ ->
               let cmd, command_knowledge = typecheck_command demands command tydef_env in
               ( cmd
               , Some (Type.negate_tyu (Type.new_constructor_tyu Raw64))
               , command_knowledge )
             | TPatVariable { unique_ids; _ } ->
               let cmd, command_knowledge = typecheck_command demands command tydef_env in
               (match type_of_usages unique_ids command_knowledge tydef_env with
                | Error msg -> raise (TypeError msg)
                | Ok None -> cmd, None, command_knowledge
                | Ok (Some result) ->
                  (* make sure that the variable is a constructed item *)
                  if not (Type.is_constructor_tyu result tydef_env)
                  then raise (TypeError "variable is not a constructed item")
                  else cmd, Some (Type.negate_tyu result), command_knowledge)
             | TTup subpats ->
               let cmd, command_knowledge = typecheck_command demands command tydef_env in
               let unique_ids = List.map (fun subpat -> subpat.unique_ids) subpats in
               let types_of_binders =
                 List.map
                   (fun ids ->
                      match type_of_usages ids command_knowledge tydef_env with
                      | Error msg -> raise (TypeError msg)
                      | Ok (Some result) -> result
                      | Ok None -> failwith "TODO: need to implement typeholes")
                   unique_ids
               in
               ( cmd
               , Some
                   (Type.negate_tyu (Type.new_constructor_tyu (Product types_of_binders)))
               , command_knowledge )
             | TConstr { tpat_name; tpat_args } ->
               (match
                  type_of_namespaced_constructor
                    tpat_name
                    (List.length tpat_args)
                    tydef_env
                with
                | None ->
                  let msg =
                    Printf.sprintf
                      "synthesize: type for variant %s with arity %d not found"
                      (Syntax.Pretty.show_name tpat_name)
                      (List.length tpat_args)
                  in
                  raise (TypeError msg)
                | Some (_ty_name, ty, polarity) ->
                  (* TODO - abstract type inference *)
                  let cmd, command_knowledge =
                    typecheck_command demands command tydef_env
                  in
                  let unique_ids =
                    List.map (fun pat_arg -> pat_arg.unique_ids) tpat_args
                  in
                  let types_of_binders =
                    List.map
                      (fun ids ->
                         match type_of_usages ids command_knowledge tydef_env with
                         | Error msg -> raise (TypeError msg)
                         | Ok (Some result) -> result
                         | Ok None -> failwith "TODO: need to implement typeholes")
                      unique_ids
                  in
                  let expected_arg_types = args_of_namespaced_variant tpat_name ty in
                  if List.length expected_arg_types <> List.length types_of_binders
                  then (
                    let msg =
                      Printf.sprintf
                        "synthesize: arity mismatch for pattern constructor %s: expected \
                         %d but got %d"
                        (Syntax.Pretty.show_name tpat_name)
                        (List.length expected_arg_types)
                        (List.length types_of_binders)
                    in
                    raise (TypeError msg))
                  else if
                    not
                      (List.for_all2
                         (fun expected_ty actual_ty ->
                            tyu_equal expected_ty actual_ty tydef_env)
                         expected_arg_types
                         types_of_binders)
                  then (
                    let msg =
                      Printf.sprintf
                        "synthesize: type mismatch for pattern constructor %s: expected \
                         argument types %s but got %s"
                        (Syntax.Pretty.show_name tpat_name)
                        (String.concat
                           ", "
                           (List.map Syntax.Pretty.show_ty_use expected_arg_types))
                        (String.concat
                           ", "
                           (List.map Syntax.Pretty.show_ty_use types_of_binders))
                    in
                    raise (TypeError msg))
                  else
                    (* we have the polarity and the type. output it. *)
                    cmd, Some (Polarised (polarity, ty)), command_knowledge)
           in
           match most_specific_type, tyu_of_pattern_opt with
           | continue, None | None, continue ->
             ( (pattern, new_command) :: branches_acc
             , continue
             , merge_contexts demands new_knowledge tydef_env )
           | Some most_specific, Some new_ty ->
             if not (tyu_equal most_specific new_ty tydef_env)
             then (
               let msg =
                 Printf.sprintf
                   "synthesize: type mismatch between matcher branches: %s vs %s"
                   (Syntax.Pretty.show_ty_use most_specific)
                   (Syntax.Pretty.show_ty_use new_ty)
               in
               raise (TypeError msg))
             else
               ( (pattern, new_command) :: branches_acc
               , Some (Type.most_specific_tyu most_specific new_ty tydef_env)
               , merge_contexts demands new_knowledge tydef_env ))
        ([], None, knowledge)
        branches
    in
    (match most_specific_type with
     | None -> assert false
     | Some tyu ->
       let expr = TMatcher (List.rev new_branches) in
       annotate expr tyu, tyu, new_knowledge)
  | TConstruction { tcons_name; tcons_args } ->
    let typ =
      type_of_namespaced_constructor tcons_name (List.length tcons_args) tydef_env
    in
    (match typ with
     | None ->
       let msg =
         Printf.sprintf
           "synthesize: type for variant %s with arity %d not found"
           (Syntax.Pretty.show_name tcons_name)
           (List.length tcons_args)
       in
       raise (TypeError msg)
     | Some (_ty_name, ty, polarity) ->
       (* TODO - abstract type inference *)
       let tyu = Ast.Polarised (polarity, ty) in
       let _, new_knowledge = check knowledge expr tyu tydef_env in
       annotate_with tyu, tyu, new_knowledge)
  | TArr terms ->
    (* ensure that each term is ty_equal with the last, and return the most
     * specific term *)
    let new_terms, most_specific_term, total_knowledge =
      List.fold_left
        (fun (terms_acc, ty_acc, ctx_acc) term ->
           let t, ty_use, term_ctx = synthesize ctx_acc term tydef_env in
           match ty_acc with
           | None ->
             t :: terms_acc, Some ty_use, merge_contexts ctx_acc term_ctx tydef_env
           | Some ty_use_acc ->
             if not (tyu_equal ty_use_acc ty_use tydef_env)
             then
               raise
                 (TypeMismatch
                    (ty_use_acc, ty_use, "synthesize: TArr terms have mismatched types"))
             else t :: terms_acc, Some ty_use, merge_contexts ctx_acc term_ctx tydef_env)
        ([], None, knowledge)
        terms
    in
    (match most_specific_term with
     | None ->
       (* Ast.Unresolved (Array Ast.Weak), []*) failwith "synthesize: TArr with no terms"
     | Some most_specific_term ->
       let expr = TArr (List.rev new_terms) in
       let tyu = Type.new_constructor_tyu (Array most_specific_term) in
       annotate expr tyu, tyu, total_knowledge)

(* workflow - given demands, check an expression with a type and output discoveries *)

and check
      (knowledge : context)
      (expr : tycheck_term)
      (expected_type : Syntax.Ast.ty_use)
      (tydef_env : tydef_env)
  : tycheck_term * context
  =
  let annotate_with_tyu expr = annotate expr expected_type in
  match expr with
  | TVariable tvar ->
    annotate_with_tyu expr, IMap.add tvar.unique_id expected_type knowledge
  | TNum _ ->
    let _, tyu, knowledge = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type tyu tydef_env
    then annotate_with_tyu expr, knowledge
    else raise (TypeMismatch (expected_type, tyu, "check: TNum expected type mismatch"))
  | TDone ->
    let _, tyu, knowledge = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type tyu tydef_env
    then annotate_with_tyu expr, knowledge
    else raise (TypeMismatch (expected_type, tyu, "check: TDone expected type mismatch"))
  | TMu (tbinder, tcommand) ->
    let tbinder_ty = Type.negate_tyu expected_type in
    let new_demands =
      List.fold_left
        (fun acc id -> IMap.add id tbinder_ty acc)
        knowledge
        tbinder.unique_ids
    in
    let updated_knowledge = merge_contexts knowledge new_demands tydef_env in
    let cmd, knowledge = typecheck_command updated_knowledge tcommand tydef_env in
    let expr = TMu (tbinder, cmd) in
    annotate expr expected_type, knowledge
  | TTuple [] ->
    let _, tyu, knowledge = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type tyu tydef_env
    then annotate_with_tyu expr, knowledge
    else
      raise (TypeMismatch (expected_type, tyu, "check: TTuple [] expected type mismatch"))
  | TTuple terms ->
    if not (Type.is_constructor_tyu expected_type tydef_env)
    then
      raise
        (TypeMismatch
           ( expected_type
           , Type.new_constructor_tyu
               (Product
                  (List.init (List.length terms) (fun _ ->
                     new_constructor_tyu (Product []))))
           , "check: TTuple expected type mismatch" ))
    else (
      let _, _, _, raw_ty = Type.tyu_to_raw_ty expected_type tydef_env in
      match raw_ty with
      | Product expected_tys ->
        if List.length terms <> List.length expected_tys
        then
          raise
            (TypeMismatch
               ( expected_type
               , Type.new_constructor_tyu (Product expected_tys)
               , "check: TTuple arity mismatch" ))
        else (
          let new_terms, knowledge =
            List.fold_left2
              (fun (terms, ctx_acc) term expected_ty ->
                 let t, term_demands = check ctx_acc term expected_ty tydef_env in
                 t :: terms, merge_contexts ctx_acc term_demands tydef_env)
              ([], knowledge)
              terms
              expected_tys
          in
          let expr = TTuple (List.rev new_terms) in
          annotate expr expected_type, knowledge)
      | _ ->
        (* TODO: a hole tyu *)
        raise
          (TypeMismatch
             ( expected_type
             , Type.new_constructor_tyu
                 (Product
                    (List.init (List.length terms) (fun _ ->
                       new_constructor_tyu (Product []))))
             , "check: TTuple expected type mismatch" )))
  | TAnn (tterm, ty_use) ->
    if tyu_equal ty_use expected_type tydef_env
    then check knowledge tterm ty_use tydef_env
    else raise (TypeMismatch (expected_type, ty_use, "check: TAnn type mismatch"))
  | TRec (tbinder, tterm) ->
    let new_demands = List.map (fun id -> id, expected_type) tbinder.unique_ids in
    let updated_knowledge =
      List.fold_left (fun acc (id, ty) -> IMap.add id ty acc) knowledge new_demands
    in
    check updated_knowledge tterm expected_type tydef_env
  (* TODO: i am pretty sure this should be check *)
  | TMatcher _ ->
    let t, ty_use, discoveries = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type ty_use tydef_env
    then t, discoveries
    else raise (TypeMismatch (expected_type, ty_use, "check: TMatcher type mismatch"))
  | TConstruction { tcons_name = _; tcons_args = _ } ->
    let t, ty_use, discoveries = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type ty_use tydef_env
    then t, discoveries
    else
      raise (TypeMismatch (expected_type, ty_use, "check: TConstruction type mismatch"))
  | TArr _terms ->
    (* placeholder implementation for arrays *)
    failwith "check: arrays not implemented"

and typecheck_command
      (knowledge : context)
      (command : tycheck_command)
      (tydef_env : tydef_env)
  : tycheck_command * context
  =
  let typecheck_command_aux l_term r_term =
    let tl_term, l_ty_use, l_knowledge = synthesize knowledge l_term tydef_env in
    let r_ty_use = Type.negate_tyu l_ty_use in
    let tr_term, final_knowledge = check l_knowledge r_term r_ty_use tydef_env in
    TCore { tl_term; tr_term }, final_knowledge
  in
  match command with
  | TCore { tl_term; tr_term } ->
    (try typecheck_command_aux tl_term tr_term with
     | Underspecified msg ->
       let warning_msg =
         Printf.sprintf
           "typecheck_command: underspecified left term, trying right term. %s"
           msg
       in
       print_endline warning_msg;
       typecheck_command_aux tr_term tl_term
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
  | TArith (TBop { top; tl_term; tr_term; tout_term }) ->
    let tout_term, out_ty_use, out_knowledge = synthesize knowledge tout_term tydef_env in
    let in_ty_use = Type.negate_tyu out_ty_use in
    let expected_in_ty = Type.new_constructor_tyu Raw64 in
    if not (tyu_equal out_ty_use (Type.negate_tyu expected_in_ty) tydef_env)
    then
      raise
        (TypeMismatch
           ( Type.negate_tyu expected_in_ty
           , out_ty_use
           , "typecheck_command: arithmetic binary operation expected raw64 output" ))
    else (
      let tl_term, left_knowledge = check out_knowledge tl_term in_ty_use tydef_env in
      let tr_term, right_knowledge = check left_knowledge tr_term in_ty_use tydef_env in
      TArith (TBop { top; tl_term; tr_term; tout_term }), right_knowledge)
  | TArith (TUnop { top; tin_term; tout_term }) ->
    let tout_term, out_ty_use, out_knowledge = synthesize knowledge tout_term tydef_env in
    let in_ty_use = Type.negate_tyu out_ty_use in
    let expected_in_ty = Type.new_constructor_tyu Raw64 in
    if not (tyu_equal out_ty_use (Type.negate_tyu expected_in_ty) tydef_env)
    then
      raise
        (TypeMismatch
           ( Type.negate_tyu expected_in_ty
           , out_ty_use
           , "typecheck_command: arithmetic unary operation expected raw64 output" ))
    else (
      let tin_term, in_knowledge = check out_knowledge tin_term in_ty_use tydef_env in
      TArith (TUnop { top; tin_term; tout_term }), in_knowledge)
  | TFork (cmd1, cmd2) ->
    let cmd1, ctx1 = typecheck_command knowledge cmd1 tydef_env in
    let cmd2, ctx2 = typecheck_command ctx1 cmd2 tydef_env in
    TFork (cmd1, cmd2), ctx2
;;

let rec tycheck_definition
          (knowledge : context)
          (def : tycheck_definition)
          (tydef_env : tydef_env)
  : tycheck_definition * context * tydef_env
  =
  match def with
  | TTermDef (tbinder, tterm) ->
    let tterm, inferred_ty, synth_knowledge = synthesize knowledge tterm tydef_env in
    let new_knowledge =
      List.fold_left
        (fun acc id -> IMap.add id inferred_ty acc)
        synth_knowledge
        tbinder.unique_ids
    in
    TTermDef (tbinder, tterm), new_knowledge, tydef_env
  | TTypeDef (tbinder, ty) ->
    let new_tydef_env = TyFrame { parent = tydef_env; var = tbinder; ty } in
    TTypeDef (tbinder, ty), knowledge, new_tydef_env
  | TModuleDef { tmod_name; tprogram } ->
    (* TODO: update outer tydef_env accessible space once Module namespacing is done *)
    let tprogram, new_insights, _ = tycheck_module knowledge tprogram tydef_env in
    TModuleDef { tmod_name; tprogram }, new_insights, tydef_env

and tycheck_module
      (knowledge : context)
      ((top_level_items, top_level_command) : tycheck_module)
      (tydef_env : tydef_env)
  : tycheck_module * context * tydef_env
  =
  let rec process_top_level_items
            (defs : tycheck_top_level_item list)
            (defs_acc : tycheck_top_level_item list)
            (knowledge_acc : context)
            (tydef_env_acc : tydef_env)
    : tycheck_top_level_item list * context * tydef_env
    =
    match defs with
    | [] -> List.rev defs_acc, knowledge_acc, tydef_env_acc
    | Def def :: rest ->
      let newdef, new_knowledge, new_tydef_env =
        tycheck_definition knowledge_acc def tydef_env_acc
      in
      process_top_level_items rest (Def newdef :: defs_acc) new_knowledge new_tydef_env
    | Open o :: rest ->
      process_top_level_items (Open o :: rest) defs_acc knowledge_acc tydef_env_acc
  in
  let new_top_level_items, after_defs_knowledge, after_defs_tydef_env =
    process_top_level_items top_level_items [] knowledge tydef_env
  in
  match top_level_command with
  | None -> (new_top_level_items, None), after_defs_knowledge, after_defs_tydef_env
  | Some command ->
    let newcmd, command_knowledge =
      typecheck_command after_defs_knowledge command after_defs_tydef_env
    in
    (new_top_level_items, Some newcmd), command_knowledge, after_defs_tydef_env
;;

let tycheck_program (modu : Ast.module_) : tycheck_module =
  let modu = tycheck_module_of_ast modu in
  let out, _, _ = tycheck_module IMap.empty modu Top in
  out
;;
