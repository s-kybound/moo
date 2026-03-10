open Syntax
open Ty_ast
open Utils.Fresh

let type_error ?loc message = raise (Syntax.Error.TypeError { loc; message })

let type_mismatch ?loc expected actual msg =
  let message =
    Printf.sprintf
      "Type error: expected %s but got %s. %s"
      (Syntax.Pretty.show_ty_use expected)
      (Syntax.Pretty.show_ty_use actual)
      msg
  in
  type_error ?loc message
;;

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
      | Top -> raise Not_found
      | Frame f ->
        if f.hole_var = var then f.usages <- usage_id :: f.usages else aux f.parent
    in
    aux frame
  | Namespaced _ ->
    () (* do nothing, the hole calculation does not need to track external names *)
;;

let get_usages_of_hole_str (frame : tycheck_hole_environment_frame) str : int list =
  let rec aux frame =
    match frame with
    | Top -> raise Not_found
    | Frame f -> if f.hole_var = str then f.usages else aux f.parent
  in
  aux frame
;;

let get_usages_of_hole (frame : tycheck_hole_environment_frame) (var : 'a Ast.binder)
  : int list
  =
  match var with
  | Ast.Wildcard _ -> []
  | Ast.Var (_, var) -> get_usages_of_hole_str frame var
;;

(* perform a co-debrujin conversion on a module *)
let tycheck_module_of_ast
      (modu : Ast.core_ann Ast.module_)
      (env : tycheck_hole_environment_frame)
  : typed_module * tycheck_hole_environment_frame
  =
  let tycheck_module_of_ast_aux (top_level_defs : Ast.core_ann Ast.module_) env
    : typed_module * tycheck_hole_environment_frame
    =
    let rec tycheck_mod_tli_of_ast (def : Ast.core_ann Ast.mod_tli) env
      : typed_mod_tli * tycheck_hole_environment_frame
      =
      match def with
      | Ast.TermDef (binder, term) ->
        let temp_binder = binder_with_ids binder None in
        let new_env = extend_hole_frame env temp_binder in
        let tterm = tycheck_term_of_ast term new_env in
        let tbinder = binder_with_ids binder None in
        Ast.TermDef (tbinder, tterm), new_env
      | Ast.TypeDef (name, abstracts, ty) -> Ast.TypeDef (name, abstracts, ty), env
      | Ast.Term term ->
        let tterm = tycheck_term_of_ast term env in
        Ast.Term tterm, env
    and tycheck_term_of_ast (term : Ast.core_ann Ast.term) env : typed_term =
      let src_ann, node = term in
      let ann = typed_ann_of_core src_ann in
      match node with
      | Ast.Mu (binder, command) ->
        let temp_binder = binder_with_ids binder None in
        let new_env = extend_hole_frame env temp_binder in
        let tcommand = tycheck_command_of_ast command new_env in
        let unique_ids =
          try get_usages_of_hole new_env temp_binder with
          | Not_found ->
            let msg =
              Printf.sprintf
                "tycheck_term_of_ast: variable %s not found in scope"
                (Syntax.Pretty.show_binder binder)
            in
            type_error ?loc:ann.loc msg
        in
        let tbinder = binder_with_ids binder (Some unique_ids) in
        mk_term ann (Ast.Mu (tbinder, tcommand))
      | Ast.Variable original_name ->
        let unique_id = genint () in
        begin try add_usage_to_hole env original_name unique_id with
        | Not_found ->
          let msg =
            Printf.sprintf
              "tycheck_term_of_ast: variable %s not found in scope"
              (Syntax.Pretty.show_name original_name)
          in
          type_error ?loc:ann.loc msg
        end;
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
               let tpat =
                 try tycheck_pattern_of_ast pat new_env with
                 | Not_found ->
                   let msg =
                     Printf.sprintf
                       "tycheck_term_of_ast: pattern variable not found in scope in \
                        pattern %s"
                       (Syntax.Pretty.show_pattern ~ann_show:(fun _ s -> s) pat)
                   in
                   type_error ?loc:ann.loc msg
               in
               tpat, tcmd)
            branches
        in
        mk_term ann (Ast.Matcher tbranches)
      | Ast.Num n -> mk_term ann (Ast.Num n)
      | Ast.Rec (binder, term) ->
        let temp_binder = binder_with_ids binder None in
        let new_env = extend_hole_frame env temp_binder in
        let tterm = tycheck_term_of_ast term new_env in
        let unique_ids =
          try get_usages_of_hole new_env temp_binder with
          | Not_found ->
            let msg =
              Printf.sprintf
                "tycheck_term_of_ast: recursive binder %s not found in scope"
                (Syntax.Pretty.show_binder binder)
            in
            type_error ?loc:ann.loc msg
        in
        if List.is_empty unique_ids
        then (
          let msg =
            Printf.sprintf
              "tycheck_term_of_ast: recursive binder %s has no usages"
              (Syntax.Pretty.show_binder binder)
          in
          type_error ?loc:ann.loc msg)
        else (
          let tbinder = binder_with_ids binder (Some unique_ids) in
          mk_term ann (Ast.Rec (tbinder, tterm)))
      | Ast.Arr terms ->
        let tterms = List.map (fun term -> tycheck_term_of_ast term env) terms in
        mk_term ann (Ast.Arr tterms)
      | Ast.Ann (term, ty_use) ->
        let tterm = tycheck_term_of_ast term env in
        mk_term ann (Ast.Ann (tterm, ty_use))
      | Ast.Exit -> mk_term ann Ast.Exit
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
          (tli : Ast.core_ann Ast.mod_tli Ast.top_level_item)
          env
      : typed_mod_tli Ast.top_level_item * tycheck_hole_environment_frame
      =
      match tli with
      | Ast.Open o -> Ast.Open o, env
      | Ast.Def d ->
        let tdef, new_env = tycheck_mod_tli_of_ast d env in
        Ast.Def tdef, new_env
    in
    let unannotated_mod_tlis, new_env, env_checkpoints =
      List.fold_left
        (fun (defs_acc, env_acc, env_checkpoints) def ->
           let def, new_env = tycheck_top_level_item_of_ast def env_acc in
           def :: defs_acc, new_env, new_env :: env_checkpoints)
        ([], env, [])
        top_level_defs
    in
    let unannotated_mod_tlis, env_checkpoints =
      List.rev unannotated_mod_tlis, List.rev env_checkpoints
    in
    let top_level_items =
      List.map2
        (fun def env_checkpoint ->
           match def with
           | Ast.Def (Ast.TermDef (tbinder, tterm)) ->
             let unique_ids = get_usages_of_hole env_checkpoint tbinder in
             Ast.Def (Ast.TermDef (set_binder_ids tbinder unique_ids, tterm))
           | _ -> def)
        unannotated_mod_tlis
        env_checkpoints
    in
    top_level_items, new_env
  in
  tycheck_module_of_ast_aux modu env
;;
