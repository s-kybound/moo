open Ast

type 'obj resolved =
  { origin_path : string list
  ; obj : 'obj
  }

type 'obj env_local =
  | Top
  | Frame of
      { parent : 'obj env_local
      ; binding : string
      ; obj : 'obj
      }

module SMap = Map.Make (String)

module SListMap = Map.Make (struct
    type t = string list

    let compare = compare
  end)

type 'obj env_module = 'obj SMap.t
type 'obj t = 'obj env_local * 'obj env_module SListMap.t

let extend_env binding obj env =
  let local_env, module_env = env in
  Frame { parent = local_env; binding; obj }, module_env
;;

let exit_env (env : 'obj t) : 'obj t option =
  let local_env, module_env = env in
  match local_env with
  | Top -> None
  | Frame { parent; _ } -> Some (parent, module_env)
;;

let resolved ?(origin_path = []) obj = { origin_path; obj }

let lookup_env_local name env =
  let rec aux env =
    match env with
    | Top -> None
    | Frame { parent; binding; obj } ->
      if binding = name then Some (resolved obj) else aux parent
  in
  aux env
;;

let lookup_env name (env : 'obj t) =
  match name with
  | Base n -> lookup_env_local n (fst env)
  | Namespaced (path, n) ->
  match SListMap.find_opt path (snd env) with
  | None -> None
  | Some mod_env ->
  match SMap.find_opt n mod_env with
  | None -> None
  | Some obj -> Some (resolved ~origin_path:path obj)
;;

let exists name env =
  match lookup_env name env with
  | None -> false
  | Some _ -> true
;;

let lookup_env_local_by_property (prop : 'obj -> bool) (env : 'obj env_local) =
  let rec aux env =
    match env with
    | Top -> None
    | Frame { parent; binding; obj } ->
      if prop obj then Some (binding, resolved obj) else aux parent
  in
  aux env
;;

let lookup_env_by_property (path : string list) (prop : 'obj -> bool) (env : 'obj t) =
  match path with
  | [] -> lookup_env_local_by_property prop (fst env)
  | _ ->
  match SListMap.find_opt path (snd env) with
  | None -> None
  | Some (mod_env : 'obj env_module) ->
    (* search through the values in the hashtable to find a match *)
    SMap.fold
      (fun binding obj acc ->
         match acc with
         | Some _ -> acc
         | None ->
           if prop obj then Some (binding, resolved ~origin_path:path obj) else None)
      mod_env
      None
;;

let module_env_of_local_env (local_env : 'obj env_local) : 'obj env_module =
  let rec aux env acc =
    match env with
    | Top -> acc
    | Frame { parent; binding; obj } ->
      (* keep only the latest values *)
      if SMap.mem binding acc
      then acc
      else (
        let new_acc = SMap.add binding obj acc in
        aux parent new_acc)
  in
  aux local_env SMap.empty
;;

let modularize_env (path : string list) (env : 'obj t) : 'obj t =
  if SListMap.mem path (snd env)
  then assert false (* make sure all paths are unique *)
  else (
    let local_env, module_env = env in
    let new_env_module = module_env_of_local_env local_env in
    let new_module_env = SListMap.add path new_env_module module_env in
    Top, new_module_env)
;;

let empty_env () : 'obj t = Top, SListMap.empty

let fold_env f env acc =
  let rec fold_env_local env acc =
    match env with
    | Top -> acc
    | Frame { parent; binding; obj } -> fold_env_local parent (f binding obj acc)
  in
  fold_env_local (fst env) acc
;;
