open Syntax
open Type
(* a cocontextual typechecker that analyses a given program *)

type tycheck_ann =
  { loc : Loc.span option
  ; ty : Ast.ty_use option
  ; unique_id : int option
  ; binder_ids : int list option
  }

type typed_ann = tycheck_ann
type typed_binder = typed_ann Ast.binder
type typed_pattern = typed_ann Ast.pattern
type typed_term = typed_ann Ast.term
type typed_command = typed_ann Ast.command
type typed_arith_command = typed_ann Ast.arith_command
type typed_definition = typed_ann Ast.definition
type typed_module = typed_ann Ast.module_

let empty_ann : typed_ann = { loc = None; ty = None; unique_id = None; binder_ids = None }
let ann_with_unique_id (id : int) : typed_ann = { empty_ann with unique_id = Some id }

let ann_with_binder_ids (ids : int list) : typed_ann =
  { empty_ann with binder_ids = Some ids }
;;

let set_term_ty ((ann, node) : typed_term) (ty : Ast.ty_use) : typed_term =
  { ann with ty = Some ty }, node
;;

let binder_ids_of_binder (b : typed_binder) : int list =
  match b with
  | Ast.Var (ann, _) | Ast.Wildcard ann -> Option.value ~default:[] ann.binder_ids
;;

let mk_var_binder (ann : typed_ann) (name : string) : typed_binder = Ast.Var (ann, name)
let mk_wild_binder (ann : typed_ann) : typed_binder = Ast.Wildcard ann
let mk_term (ann : typed_ann) (node : typed_ann Ast.term_node) : typed_term = ann, node

let mk_command (ann : typed_ann) (node : typed_ann Ast.command_node) : typed_command =
  ann, node
;;

let typed_ann_of_core (ann : Ast.core_ann) : typed_ann = { empty_ann with loc = ann.loc }

let binder_with_ids (b : Ast.core_ann Ast.binder) (ids : int list option) : typed_binder =
  let ann_of_ids base_ann =
    match ids with
    | None -> base_ann
    | Some ids -> { base_ann with binder_ids = Some ids }
  in
  match b with
  | Ast.Var (src_ann, name) -> Ast.Var (ann_of_ids (typed_ann_of_core src_ann), name)
  | Ast.Wildcard src_ann -> Ast.Wildcard (ann_of_ids (typed_ann_of_core src_ann))
;;

let set_binder_ids (b : typed_binder) (ids : int list) : typed_binder =
  match b with
  | Ast.Var (_ann, name) -> Ast.Var ({ empty_ann with binder_ids = Some ids }, name)
  | Ast.Wildcard _ann -> Ast.Wildcard { empty_ann with binder_ids = Some ids }
;;

let pattern_with_empty_ids (pat : Ast.core_ann Ast.pattern) : typed_pattern =
  match pat with
  | Ast.Numeral n -> Ast.Numeral n
  | Ast.Binder binder -> Ast.Binder (binder_with_ids binder None)
  | Ast.Tup binders -> Ast.Tup (List.map (fun b -> binder_with_ids b None) binders)
  | Ast.Constr { pat_name; pat_args } ->
    Ast.Constr
      { pat_name; pat_args = List.map (fun b -> binder_with_ids b None) pat_args }
;;

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

let extend_hole_frame (parent : tycheck_hole_environment_frame) (hole_var : 'a Ast.binder)
  : tycheck_hole_environment_frame
  =
  match hole_var with
  | Ast.Var (_, var) -> Frame { parent; hole_var = var; usages = [] }
  | Ast.Wildcard _ -> parent
;;

let extend_pattern_frame (parent : tycheck_hole_environment_frame) (pat : 'a Ast.pattern)
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

let get_usages_of_hole (frame : tycheck_hole_environment_frame) (var : 'a Ast.binder)
  : int list
  =
  match var with
  | Ast.Wildcard _ -> []
  | Ast.Var (_, var) ->
    let rec aux frame =
      match frame with
      | Top -> failwith "get_usages_of_hole: hole variable not found"
      | Frame f -> if f.hole_var = var then f.usages else aux f.parent
    in
    aux frame
;;

(* perform a co-debrujin conversion on a module *)
let tycheck_module_of_ast (modu : Ast.core_ann Ast.module_) : typed_module =
  let rec tycheck_module_of_ast_aux
            ((top_level_defs, top_level_command) : Ast.core_ann Ast.module_)
            env
    : typed_module
    =
    let rec tycheck_definition_of_ast (def : Ast.core_ann Ast.definition) env
      : typed_definition * tycheck_hole_environment_frame
      =
      match def with
      | Ast.TermDef (binder, term) ->
        let temp_binder = binder_with_ids binder None in
        let new_env = extend_hole_frame env temp_binder in
        let tterm = tycheck_term_of_ast term new_env in
        (* needs a second pass to get the unique ids *)
        let tbinder = binder_with_ids binder None in
        Ast.TermDef (tbinder, tterm), new_env
      | Ast.TypeDef (kind_binder, ty) -> Ast.TypeDef (kind_binder, ty), env
      | Ast.ModuleDef { name; program } ->
        let tprogram = tycheck_module_of_ast_aux program env in
        Ast.ModuleDef { name; program = tprogram }, env
    and tycheck_term_of_ast (term : Ast.core_ann Ast.term) env : typed_term =
      let src_ann, node = term in
      let ann = typed_ann_of_core src_ann in
      match node with
      | Ast.Mu (binder, command) ->
        let temp_binder = binder_with_ids binder None in
        let new_env = extend_hole_frame env temp_binder in
        let tcommand = tycheck_command_of_ast command new_env in
        let unique_ids = get_usages_of_hole new_env temp_binder in
        let tbinder = binder_with_ids binder (Some unique_ids) in
        mk_term ann (Ast.Mu (tbinder, tcommand))
      | Ast.Variable original_name ->
        let unique_id = gen_int () in
        add_usage_to_hole env original_name unique_id;
        mk_term
          { (ann_with_unique_id unique_id) with loc = ann.loc }
          (Ast.Variable original_name)
      | Ast.Construction { cons_name; cons_args } ->
        let tcons_args = List.map (fun arg -> tycheck_term_of_ast arg env) cons_args in
        mk_term ann (Ast.Construction { cons_name; cons_args = tcons_args })
      | Ast.Tuple terms ->
        let tterms = List.map (fun term -> tycheck_term_of_ast term env) terms in
        mk_term ann (Ast.Tuple tterms)
      | Ast.Matcher branches ->
        let tbranches =
          List.map
            (fun (pat, cmd) ->
               let seed_pat = pattern_with_empty_ids pat in
               let new_env = extend_pattern_frame env seed_pat in
               let tcmd = tycheck_command_of_ast cmd new_env in
               let tpat = tycheck_pattern_of_ast pat new_env in
               tpat, tcmd)
            branches
        in
        mk_term ann (Ast.Matcher tbranches)
      | Ast.Num n -> mk_term ann (Ast.Num n)
      | Ast.Rec (binder, term) ->
        let temp_binder = binder_with_ids binder None in
        let new_env = extend_hole_frame env temp_binder in
        let tterm = tycheck_term_of_ast term new_env in
        let unique_ids = get_usages_of_hole new_env temp_binder in
        if List.is_empty unique_ids
        then (
          let msg =
            Printf.sprintf
              "tycheck_term_of_ast: recursive binder %s has no usages"
              (Syntax.Pretty.show_binder binder)
          in
          failwith msg)
        else (
          let tbinder = binder_with_ids binder (Some unique_ids) in
          mk_term ann (Ast.Rec (tbinder, tterm)))
      | Ast.Arr terms ->
        let tterms = List.map (fun term -> tycheck_term_of_ast term env) terms in
        mk_term ann (Ast.Arr tterms)
      | Ast.Ann (term, ty_use) ->
        let tterm = tycheck_term_of_ast term env in
        mk_term ann (Ast.Ann (tterm, ty_use))
      | Ast.Done -> mk_term ann Ast.Done
    and tycheck_command_of_ast (command : Ast.core_ann Ast.command) env : typed_command =
      let src_ann, node = command in
      let ann = typed_ann_of_core src_ann in
      match node with
      | Ast.Core { l_term; r_term } ->
        let tl_term = tycheck_term_of_ast l_term env in
        let tr_term = tycheck_term_of_ast r_term env in
        mk_command ann (Ast.Core { l_term = tl_term; r_term = tr_term })
      | Ast.Arith arith_cmd ->
        (match arith_cmd with
         | Ast.Unop { op; in_term; out_term } ->
           let tin_term = tycheck_term_of_ast in_term env in
           let tout_term = tycheck_term_of_ast out_term env in
           mk_command
             ann
             (Ast.Arith (Ast.Unop { op; in_term = tin_term; out_term = tout_term }))
         | Ast.Bop { op; l_term; r_term; out_term } ->
           let tl_term = tycheck_term_of_ast l_term env in
           let tr_term = tycheck_term_of_ast r_term env in
           let tout_term = tycheck_term_of_ast out_term env in
           mk_command
             ann
             (Ast.Arith
                (Ast.Bop { op; l_term = tl_term; r_term = tr_term; out_term = tout_term })))
      | Ast.Fork (cmd1, cmd2) ->
        let tcmd1 = tycheck_command_of_ast cmd1 env in
        let tcmd2 = tycheck_command_of_ast cmd2 env in
        mk_command ann (Ast.Fork (tcmd1, tcmd2))
    and tycheck_pattern_of_ast (pat : Ast.core_ann Ast.pattern) env : typed_pattern =
      match pat with
      | Ast.Numeral n -> Ast.Numeral n
      | Ast.Binder binder ->
        let temp_binder = binder_with_ids binder None in
        let unique_ids = get_usages_of_hole env temp_binder in
        Ast.Binder (binder_with_ids binder (Some unique_ids))
      | Ast.Tup pat_binders ->
        let tpat_binders =
          List.map
            (fun pat_binder ->
               let temp_binder = binder_with_ids pat_binder None in
               let unique_ids = get_usages_of_hole env temp_binder in
               binder_with_ids pat_binder (Some unique_ids))
            pat_binders
        in
        Ast.Tup tpat_binders
      | Ast.Constr { pat_name; pat_args } ->
        let tpat_args =
          List.map
            (fun pat_binder ->
               let temp_binder = binder_with_ids pat_binder None in
               let unique_ids = get_usages_of_hole env temp_binder in
               binder_with_ids pat_binder (Some unique_ids))
            pat_args
        in
        Ast.Constr { pat_name; pat_args = tpat_args }
    and tycheck_top_level_item_of_ast
          (tli : Ast.core_ann Ast.definition Ast.top_level_item)
          env
      : typed_definition Ast.top_level_item * tycheck_hole_environment_frame
      =
      match tli with
      | Ast.Open o -> Ast.Open o, env
      | Ast.Def d ->
        let tdef, new_env = tycheck_definition_of_ast d env in
        Ast.Def tdef, new_env
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
           | Ast.Def (Ast.TermDef (tbinder, tterm)) ->
             let unique_ids = get_usages_of_hole env_checkpoint tbinder in
             Ast.Def (Ast.TermDef (set_binder_ids tbinder unique_ids, tterm))
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

exception
  TypeError of
    { loc : Loc.span option
    ; message : string
    }

exception Underspecified of string

let type_error ?loc message = raise (TypeError { loc; message })
let annotate (term : typed_term) (tyu : Ast.ty_use) : typed_term = set_term_ty term tyu

(* Workflow - synthesize takes in a set of invariants, and determines the type of an expression.
 *            it returns the demands in order to have that expression have that type 
 *            it also returns the annotated terms themselves *)
let rec synthesize (knowledge : context) (expr : typed_term) (tydef_env : tydef_env)
  : typed_term * Syntax.Ast.ty_use * context
  =
  let annotate_with = annotate expr in
  let ann, node = expr in
  match node with
  | Ast.Variable original_name ->
    (match ann.unique_id with
     | None -> assert false
     | Some unique_id ->
     match IMap.find_opt unique_id knowledge with
     | Some ty_use -> annotate_with ty_use, ty_use, knowledge
     | None ->
       let msg =
         Printf.sprintf
           "synthesize: variable %s not found in context"
           (Syntax.Pretty.show_name original_name)
       in
       raise (Underspecified msg))
  | Ast.Num _ ->
    let tyu = Type.new_constructor_tyu Raw64 in
    annotate_with tyu, tyu, knowledge
  | Ast.Done ->
    let tyu = Type.negate_tyu (Type.new_constructor_tyu (Product [])) in
    annotate_with tyu, tyu, knowledge
  | Ast.Tuple [] ->
    let tyu = Type.new_constructor_tyu (Product []) in
    annotate_with tyu, tyu, knowledge
  | Ast.Tuple terms ->
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
    annotate (ann, Ast.Tuple terms) tyu, tyu, new_knowledge
  | Ast.Ann (tterm, ty_use) ->
    let _, demands = check knowledge tterm ty_use tydef_env in
    expr, ty_use, demands
  | Ast.Rec (tbinder, tterm) ->
    let _, inferred_ty, demands = synthesize knowledge tterm tydef_env in
    let relevant_ids = binder_ids_of_binder tbinder in
    (match type_of_usages relevant_ids demands tydef_env with
     | Ok None -> raise (Underspecified "synthesize: no demands found for rec binder")
     | Error msg -> type_error ?loc:ann.loc msg
     | Ok (Some ty_use) ->
       let tyu = most_specific_tyu inferred_ty ty_use tydef_env in
       annotate_with tyu, tyu, demands)
  | Ast.Mu (tbinder, tcommand) ->
    let tcommand, new_knowledge = typecheck_command knowledge tcommand tydef_env in
    let relevant_ids = binder_ids_of_binder tbinder in
    (match type_of_usages relevant_ids new_knowledge tydef_env with
     | Ok None -> raise (Underspecified "synthesize: no demands found for mu binder")
     | Error msg -> type_error ?loc:ann.loc msg
     | Ok (Some ty_use) ->
       let tyu = Type.negate_tyu ty_use in
       let expr = ann, Ast.Mu (tbinder, tcommand) in
       annotate expr tyu, tyu, new_knowledge)
  | Ast.Matcher branches ->
    let new_branches, most_specific_type, new_knowledge =
      List.fold_left
        (fun (branches_acc, most_specific_type, demands) (pattern, command) ->
           let new_command, tyu_of_pattern_opt, new_knowledge =
             match pattern with
             | Ast.Numeral _ ->
               let cmd, command_knowledge = typecheck_command demands command tydef_env in
               ( cmd
               , Some (Type.negate_tyu (Type.new_constructor_tyu Raw64))
               , command_knowledge )
             | Ast.Binder binder ->
               let unique_ids = binder_ids_of_binder binder in
               let cmd, command_knowledge = typecheck_command demands command tydef_env in
               begin match type_of_usages unique_ids command_knowledge tydef_env with
               | Error msg -> type_error ?loc:ann.loc msg
               | Ok None -> cmd, None, command_knowledge
               | Ok (Some result) ->
                 (* make sure that the variable is a constructed item *)
                 if not (Type.is_constructor_tyu result tydef_env)
                 then type_error ?loc:ann.loc "variable is not a constructed item"
                 else cmd, Some (Type.negate_tyu result), command_knowledge
               end
             | Ast.Tup subpats ->
               let cmd, command_knowledge = typecheck_command demands command tydef_env in
               let unique_ids = List.map binder_ids_of_binder subpats in
               let types_of_binders =
                 List.map
                   (fun ids ->
                      match type_of_usages ids command_knowledge tydef_env with
                      | Error msg -> type_error ?loc:ann.loc msg
                      | Ok (Some result) -> result
                      | Ok None -> failwith "TODO: need to implement typeholes")
                   unique_ids
               in
               ( cmd
               , Some
                   (Type.negate_tyu (Type.new_constructor_tyu (Product types_of_binders)))
               , command_knowledge )
             | Ast.Constr { pat_name; pat_args } ->
             match
               type_of_namespaced_constructor pat_name (List.length pat_args) tydef_env
             with
             | None ->
               let msg =
                 Printf.sprintf
                   "synthesize: type for variant %s with arity %d not found"
                   (Syntax.Pretty.show_name pat_name)
                   (List.length pat_args)
               in
               type_error ?loc:ann.loc msg
             | Some (_ty_name, ty, polarity) ->
               (* TODO - abstract type inference *)
               let cmd, command_knowledge = typecheck_command demands command tydef_env in
               let unique_ids = List.map binder_ids_of_binder pat_args in
               let types_of_binders =
                 List.map
                   (fun ids ->
                      match type_of_usages ids command_knowledge tydef_env with
                      | Error msg -> type_error ?loc:ann.loc msg
                      | Ok (Some result) -> result
                      | Ok None -> failwith "TODO: need to implement typeholes")
                   unique_ids
               in
               let expected_arg_types = args_of_namespaced_variant pat_name ty in
               if List.length expected_arg_types <> List.length types_of_binders
               then (
                 let msg =
                   Printf.sprintf
                     "synthesize: arity mismatch for pattern constructor %s: expected %d \
                      but got %d"
                     (Syntax.Pretty.show_name pat_name)
                     (List.length expected_arg_types)
                     (List.length types_of_binders)
                 in
                 type_error ?loc:ann.loc msg)
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
                     (Syntax.Pretty.show_name pat_name)
                     (String.concat
                        ", "
                        (List.map Syntax.Pretty.show_ty_use expected_arg_types))
                     (String.concat
                        ", "
                        (List.map Syntax.Pretty.show_ty_use types_of_binders))
                 in
                 type_error ?loc:ann.loc msg)
               else
                 (* we have the polarity and the type. output it. *)
                 cmd, Some (Polarised (polarity, ty)), command_knowledge
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
               type_error ?loc:ann.loc msg)
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
       let expr = ann, Ast.Matcher (List.rev new_branches) in
       annotate expr tyu, tyu, new_knowledge)
  | Ast.Construction { cons_name = tcons_name; cons_args = tcons_args } ->
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
       type_error ?loc:ann.loc msg
     | Some (_ty_name, ty, polarity) ->
       (* TODO - abstract type inference *)
       let tyu = Ast.Polarised (polarity, ty) in
       let _, new_knowledge = check knowledge expr tyu tydef_env in
       annotate_with tyu, tyu, new_knowledge)
  | Ast.Arr terms ->
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
       let expr = ann, Ast.Arr (List.rev new_terms) in
       let tyu = Type.new_constructor_tyu (Array most_specific_term) in
       annotate expr tyu, tyu, total_knowledge)

(* workflow - given demands, check an expression with a type and output discoveries *)

and check
      (knowledge : context)
      (expr : typed_term)
      (expected_type : Syntax.Ast.ty_use)
      (tydef_env : tydef_env)
  : typed_term * context
  =
  let annotate_with_tyu expr = annotate expr expected_type in
  let ann, node = expr in
  match node with
  | Ast.Variable _ ->
    (match ann.unique_id with
     | None -> assert false
     | Some unique_id ->
       annotate_with_tyu expr, IMap.add unique_id expected_type knowledge)
  | Ast.Num _ ->
    let _, tyu, knowledge = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type tyu tydef_env
    then annotate_with_tyu expr, knowledge
    else raise (TypeMismatch (expected_type, tyu, "check: TNum expected type mismatch"))
  | Ast.Done ->
    let _, tyu, knowledge = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type tyu tydef_env
    then annotate_with_tyu expr, knowledge
    else raise (TypeMismatch (expected_type, tyu, "check: TDone expected type mismatch"))
  | Ast.Mu (tbinder, tcommand) ->
    let tbinder_ty = Type.negate_tyu expected_type in
    let new_demands =
      List.fold_left
        (fun acc id -> IMap.add id tbinder_ty acc)
        knowledge
        (binder_ids_of_binder tbinder)
    in
    let updated_knowledge = merge_contexts knowledge new_demands tydef_env in
    let cmd, knowledge = typecheck_command updated_knowledge tcommand tydef_env in
    let expr = ann, Ast.Mu (tbinder, cmd) in
    annotate expr expected_type, knowledge
  | Ast.Tuple [] ->
    let _, tyu, knowledge = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type tyu tydef_env
    then annotate_with_tyu expr, knowledge
    else
      raise (TypeMismatch (expected_type, tyu, "check: TTuple [] expected type mismatch"))
  | Ast.Tuple terms ->
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
          let expr = ann, Ast.Tuple (List.rev new_terms) in
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
  | Ast.Ann (tterm, ty_use) ->
    if tyu_equal ty_use expected_type tydef_env
    then check knowledge tterm ty_use tydef_env
    else raise (TypeMismatch (expected_type, ty_use, "check: TAnn type mismatch"))
  | Ast.Rec (tbinder, tterm) ->
    let new_demands =
      List.map (fun id -> id, expected_type) (binder_ids_of_binder tbinder)
    in
    let updated_knowledge =
      List.fold_left (fun acc (id, ty) -> IMap.add id ty acc) knowledge new_demands
    in
    check updated_knowledge tterm expected_type tydef_env
  (* TODO: i am pretty sure this should be check *)
  | Ast.Matcher _ ->
    let t, ty_use, discoveries = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type ty_use tydef_env
    then t, discoveries
    else raise (TypeMismatch (expected_type, ty_use, "check: TMatcher type mismatch"))
  | Ast.Construction { cons_name = _; cons_args = _ } ->
    let t, ty_use, discoveries = synthesize knowledge expr tydef_env in
    if tyu_equal expected_type ty_use tydef_env
    then t, discoveries
    else
      raise (TypeMismatch (expected_type, ty_use, "check: TConstruction type mismatch"))
  | Ast.Arr _terms ->
    (* placeholder implementation for arrays *)
    failwith "check: arrays not implemented"

and typecheck_command
      (knowledge : context)
      (command : typed_command)
      (tydef_env : tydef_env)
  : typed_command * context
  =
  let typecheck_command_aux l_term r_term ann =
    let tl_term, l_ty_use, l_knowledge = synthesize knowledge l_term tydef_env in
    let r_ty_use = Type.negate_tyu l_ty_use in
    let tr_term, final_knowledge = check l_knowledge r_term r_ty_use tydef_env in
    mk_command ann (Ast.Core { l_term = tl_term; r_term = tr_term }), final_knowledge
  in
  let ann, node = command in
  match node with
  | Ast.Core { l_term; r_term } ->
    (try typecheck_command_aux l_term r_term ann with
     | Underspecified msg ->
       let warning_msg =
         Printf.sprintf
           "typecheck_command: underspecified left term, trying right term. %s"
           msg
       in
       print_endline warning_msg;
       typecheck_command_aux r_term l_term ann
     | TypeMismatch (expected, actual, msg) ->
       let msg =
         Printf.sprintf
           "Type mismatch in TCore: expected %s but got %s. %s"
           (Syntax.Pretty.show_ty_use expected)
           (Syntax.Pretty.show_ty_use actual)
           msg
       in
       type_error ?loc:ann.loc msg
     | e -> raise e)
  | Ast.Arith
      (Ast.Bop { op = top; l_term = tl_term; r_term = tr_term; out_term = tout_term }) ->
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
      ( mk_command
          ann
          (Ast.Arith
             (Ast.Bop
                { op = top; l_term = tl_term; r_term = tr_term; out_term = tout_term }))
      , right_knowledge ))
  | Ast.Arith (Ast.Unop { op = top; in_term = tin_term; out_term = tout_term }) ->
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
      ( mk_command
          ann
          (Ast.Arith (Ast.Unop { op = top; in_term = tin_term; out_term = tout_term }))
      , in_knowledge ))
  | Ast.Fork (cmd1, cmd2) ->
    let cmd1, ctx1 = typecheck_command knowledge cmd1 tydef_env in
    let cmd2, ctx2 = typecheck_command ctx1 cmd2 tydef_env in
    mk_command ann (Ast.Fork (cmd1, cmd2)), ctx2
;;

let rec tycheck_definition
          (knowledge : context)
          (def : typed_definition)
          (tydef_env : tydef_env)
  : typed_definition * context * tydef_env
  =
  match def with
  | Ast.TermDef (tbinder, tterm) ->
    let tterm, inferred_ty, synth_knowledge = synthesize knowledge tterm tydef_env in
    let new_knowledge =
      List.fold_left
        (fun acc id -> IMap.add id inferred_ty acc)
        synth_knowledge
        (binder_ids_of_binder tbinder)
    in
    Ast.TermDef (tbinder, tterm), new_knowledge, tydef_env
  | Ast.TypeDef (tbinder, ty) ->
    let new_tydef_env = TyFrame { parent = tydef_env; var = tbinder; ty } in
    Ast.TypeDef (tbinder, ty), knowledge, new_tydef_env
  | Ast.ModuleDef { name; program } ->
    (* TODO: update outer tydef_env accessible space once Module namespacing is done *)
    let tprogram, new_insights, _ = tycheck_module knowledge program tydef_env in
    Ast.ModuleDef { name; program = tprogram }, new_insights, tydef_env

and tycheck_module
      (knowledge : context)
      ((top_level_items, top_level_command) : typed_module)
      (tydef_env : tydef_env)
  : typed_module * context * tydef_env
  =
  let rec process_top_level_items
            (defs : typed_definition Ast.top_level_item list)
            (defs_acc : typed_definition Ast.top_level_item list)
            (knowledge_acc : context)
            (tydef_env_acc : tydef_env)
    : typed_definition Ast.top_level_item list * context * tydef_env
    =
    match defs with
    | [] -> List.rev defs_acc, knowledge_acc, tydef_env_acc
    | Ast.Def def :: rest ->
      let newdef, new_knowledge, new_tydef_env =
        tycheck_definition knowledge_acc def tydef_env_acc
      in
      process_top_level_items
        rest
        (Ast.Def newdef :: defs_acc)
        new_knowledge
        new_tydef_env
    | Ast.Open o :: rest ->
      process_top_level_items (Ast.Open o :: rest) defs_acc knowledge_acc tydef_env_acc
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

let tycheck_program (modu : Ast.core_ann Ast.module_) : typed_module * tydef_env =
  let modu = tycheck_module_of_ast modu in
  let out, _, env = tycheck_module IMap.empty modu Top in
  out, env
;;

(* TODO: make the resolver *)
