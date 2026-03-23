(* Replaces use names with actual module paths. 
 *)
open Syntax.Ast

(* An internal map for storing replacement mappings. 
 * Unique for each module. *)
type replacement_map = (string list, string list) Hashtbl.t
type 'ann resolved = Resolved of 'ann module_

let rec replace_module_aux (rep_map : replacement_map) (m : 'ann module_) : 'ann module_ =
  let rec replace_name rep_map name =
    match name with
    | Base n -> Base n
    | Namespaced (path, n) ->
    match Hashtbl.find_opt rep_map path with
    | Some new_path -> Namespaced (new_path, n)
    | None -> Namespaced (path, n)
  and replace_term rep_map (ann, term_node) =
    let new_term_node =
      match term_node with
      | Mu (binder, cmd) -> Mu (binder, replace_command rep_map cmd)
      | Variable name -> Variable (replace_name rep_map name)
      | Construction { cons_name; cons_args } ->
        Construction
          { cons_name = replace_name rep_map cons_name
          ; cons_args = List.map (fun t -> replace_term rep_map t) cons_args
          }
      | Tuple terms -> Tuple (List.map (replace_term rep_map) terms)
      | Matcher branches ->
        Matcher
          (List.map
             (fun (pat, cmd) -> replace_pattern rep_map pat, replace_command rep_map cmd)
             branches)
      | Num n -> Num n
      | Rec (binder, term) -> Rec (binder, replace_term rep_map term)
      | Arr terms -> Arr (List.map (replace_term rep_map) terms)
      | Ann (term, ty) -> Ann (replace_term rep_map term, replace_tyu rep_map ty)
      | Exit -> Exit
    in
    ann, new_term_node
  and replace_ty rep_map ty =
    match ty with
    | Named (n, args) ->
      Named (replace_name rep_map n, List.map (replace_tyu rep_map) args)
    | Raw (mode, shape, raw_ty) -> Raw (mode, shape, replace_raw_ty rep_map raw_ty)
  and replace_tyu rep_map tyu =
    match tyu with
    | Polarised (pol, ty) -> Polarised (pol, replace_ty rep_map ty)
    | AbstractIntroducer (unify_ty, ty_use) ->
      AbstractIntroducer (unify_ty, replace_tyu rep_map ty_use)
    | Abstract _ -> tyu
    | Weak _ -> tyu
  and replace_raw_ty rep_map raw_ty =
    match raw_ty with
    | Int -> Int
    | Product tys -> Product (List.map (replace_tyu rep_map) tys)
    | Array ty -> Array (replace_tyu rep_map ty)
    | Variant variants ->
      Variant
        (List.map
           (fun { constr_name; constr_args } ->
              { constr_name; constr_args = List.map (replace_tyu rep_map) constr_args })
           variants)
  and replace_command rep_map (ann, cmd_node) =
    let new_cmd_node =
      match cmd_node with
      | Core { l_term; r_term } ->
        Core
          { l_term = replace_term rep_map l_term; r_term = replace_term rep_map r_term }
      | Fork (cmd1, cmd2) ->
        Fork (replace_command rep_map cmd1, replace_command rep_map cmd2)
      | Arith arith_cmd ->
        let new_arith_cmd =
          match arith_cmd with
          | Unop { op; in_term; out_term } ->
            Unop
              { op
              ; in_term = replace_term rep_map in_term
              ; out_term = replace_term rep_map out_term
              }
          | Bop { op; l_term; r_term; out_term } ->
            Bop
              { op
              ; l_term = replace_term rep_map l_term
              ; r_term = replace_term rep_map r_term
              ; out_term = replace_term rep_map out_term
              }
        in
        Arith new_arith_cmd
    in
    ann, new_cmd_node
  and replace_pattern rep_map pat =
    match pat with
    | Binder binder -> Binder binder
    | Tup binders -> Tup binders
    | Constr { pat_name; pat_args } ->
      Constr { pat_name = replace_name rep_map pat_name; pat_args }
    | Numeral n -> Numeral n
  in
  match m with
  | [] -> m
  | Open (Use { mod_name; use_name }) :: rest ->
    let mod_path =
      match mod_name with
      | Base n -> [ n ]
      | Namespaced (path, n) -> path @ [ n ]
    in
    Hashtbl.add rep_map [ use_name ] mod_path;
    Open (Use { mod_name; use_name }) :: replace_module_aux rep_map rest
  | Def tli :: rest ->
    let new_tli =
      match tli with
      | TermDef (binder, term) -> TermDef (binder, replace_term rep_map term)
      | TypeDef (name, params, ty) -> TypeDef (name, params, replace_ty rep_map ty)
      | Term term -> Term (replace_term rep_map term)
    in
    Def new_tli :: replace_module_aux rep_map rest
;;

let replace_module (m : 'ann module_) : 'ann resolved =
  Resolved (replace_module_aux (Hashtbl.create 10) m)
;;
