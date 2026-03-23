(* Takes an unresolved module,
 * resolves it's module usages,
 * finally determines the required dependencies
 * for the module.
 *)
open Syntax.Ast
open Resolver

exception CyclicDependency of string list list

module StringList = struct
  type t = string list

  let compare = compare
end

module DependencySet = Set.Make (StringList)

let rec dependencies_of_module_aux (set : DependencySet.t) (m : 'ann module_)
  : DependencySet.t
  =
  let rec dependencies_of_name set name : DependencySet.t =
    match name with
    | Base _ -> set
    | Namespaced (path, _) -> DependencySet.add path set
  and dependencies_of_term set (_, term_node) : DependencySet.t =
    match term_node with
    | Mu (_, cmd) -> dependencies_of_command set cmd
    | Variable name -> dependencies_of_name set name
    | Construction { cons_name; cons_args } ->
      let new_set = dependencies_of_name set cons_name in
      List.fold_left dependencies_of_term new_set cons_args
      (* If the construction <*)
    | Tuple terms -> List.fold_left dependencies_of_term set terms
    | Matcher branches ->
      List.fold_left
        (fun acc (pat, cmd) ->
           let acc' = dependencies_of_pattern acc pat in
           dependencies_of_command acc' cmd)
        set
        branches
    | Num _ -> set
    | Rec (_, term) -> dependencies_of_term set term
    | Arr terms -> List.fold_left dependencies_of_term set terms
    | Ann (term, ty) ->
      let set' = dependencies_of_term set term in
      dependencies_of_tyu set' ty
    | Exit -> set
  and dependencies_of_ty set (ty : ty) : DependencySet.t =
    match ty with
    | Named (n, args) ->
      let new_set = dependencies_of_name set n in
      List.fold_left dependencies_of_tyu new_set args
    | Raw (_, _, raw_ty) -> dependencies_of_raw_ty set raw_ty
  and dependencies_of_tyu set (tyu : ty_use) : DependencySet.t =
    match tyu with
    | Polarised (_, ty) -> dependencies_of_ty set ty
    | AbstractIntroducer (_, ty_use) -> dependencies_of_tyu set ty_use
    | Abstract _ -> set
    | Weak _ -> set
  and dependencies_of_raw_ty set (raw_ty : raw_ty) : DependencySet.t =
    match raw_ty with
    | Int -> set
    | Product tys -> List.fold_left dependencies_of_tyu set tys
    | Array ty -> dependencies_of_tyu set ty
    | Variant variants ->
      List.fold_left
        (fun acc { constr_args; _ } -> List.fold_left dependencies_of_tyu acc constr_args)
        set
        variants
  and dependencies_of_command set (_, cmd_node) : DependencySet.t =
    match cmd_node with
    | Core { l_term; r_term } ->
      let set' = dependencies_of_term set l_term in
      dependencies_of_term set' r_term
    | Fork (cmd1, cmd2) ->
      let set' = dependencies_of_command set cmd1 in
      dependencies_of_command set' cmd2
    | Arith (Unop { in_term; out_term; _ }) ->
      let set' = dependencies_of_term set in_term in
      dependencies_of_term set' out_term
    | Arith (Bop { l_term; r_term; out_term; _ }) ->
      let set' = dependencies_of_term set l_term in
      let set'' = dependencies_of_term set' r_term in
      dependencies_of_term set'' out_term
  and dependencies_of_pattern set (pat : 'ann pattern) : DependencySet.t =
    match pat with
    | Constr { pat_name; _ } -> dependencies_of_name set pat_name
    | Binder _ | Tup _ | Numeral _ -> set
  in
  match m with
  | [] -> set
  | Open _ :: _ ->
    assert false (* Open statements should have been resolved by this point. *)
  | Def tli :: rest ->
  match tli with
  | TermDef (_, term) -> dependencies_of_module_aux (dependencies_of_term set term) rest
  | TypeDef (_, _, ty) -> dependencies_of_module_aux (dependencies_of_ty set ty) rest
  | Term term -> dependencies_of_module_aux (dependencies_of_term set term) rest
;;

let dependencies_of_resolved (resolved : 'ann resolved) : DependencySet.t * 'ann module_ =
  let (Resolved m_) = resolved in
  dependencies_of_module_aux DependencySet.empty m_, m_
;;

type 'ann dependency_graph = (string list, DependencySet.t * 'ann module_) Hashtbl.t

let dependency_graph_of_resolved (resolveds : (string list * 'ann resolved) list)
  : 'ann dependency_graph
  =
  let graph = Hashtbl.create (List.length resolveds) in
  List.iter
    (fun (mod_name, resolved) ->
       let deps, m = dependencies_of_resolved resolved in
       Hashtbl.add graph mod_name (deps, m))
    resolveds;
  graph
;;

type traversal_state =
  | Visiting
  | Visited

let dfs_toposort (resolveds : (string list * 'ann resolved) list)
  : (string list * 'ann module_) list
  =
  let graph = dependency_graph_of_resolved resolveds in
  let (visited : (string list, traversal_state) Hashtbl.t) =
    Hashtbl.create (Hashtbl.length graph)
  in
  let result = ref [] in
  let rec visit (curr_path : string list list) (mod_name : string list) =
    match Hashtbl.find_opt visited mod_name with
    | Some Visited -> () (* Already processed this module, skip *)
    | None ->
      Hashtbl.add visited mod_name Visiting;
      let deps, m = Hashtbl.find graph mod_name in
      DependencySet.iter (visit (mod_name :: curr_path)) deps;
      Hashtbl.replace visited mod_name Visited;
      result := (mod_name, m) :: !result
    | Some Visiting ->
    match curr_path with
    | [] ->
      assert false
      (* This should't happen, we are in a path where we see 
       * the module name again, so there must be at least one module *)
    | cyclic :: _ ->
      curr_path
      |> List.rev
      |> List.drop_while (fun name -> name <> cyclic)
        (* this trims the path to only include the cycle *)
      |> fun cycle -> raise (CyclicDependency cycle)
  in
  Hashtbl.iter
    (fun mod_name _ -> if not (Hashtbl.mem visited mod_name) then visit [] mod_name)
    graph;
  List.rev !result
;;
