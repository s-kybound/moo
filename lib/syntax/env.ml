open Ast

type ('binding, 'obj) env_local =
  | Top
  | Frame of
      { parent : ('binding, 'obj) env_local
      ; binding : 'binding
      ; obj : 'obj
      }

type ('binding, 'obj) env_module = ('binding, 'obj) Hashtbl.t

type ('binding, 'obj) t =
  ('binding, 'obj) env_local * (string list, ('binding, 'obj) env_module) Hashtbl.t

let extend_env binding obj env =
  let local_env, module_env = env in
  Frame { parent = local_env; binding; obj }, module_env
;;

let exit_env (env : ('binding, 'obj) t) : ('binding, 'obj) t option =
  let local_env, module_env = env in
  match local_env with
  | Top -> None
  | Frame { parent; _ } -> Some (parent, module_env)
;;

let lookup_env_local name env =
  let rec aux env =
    match env with
    | Top -> None
    | Frame { parent; binding; obj } -> if binding = name then Some obj else aux parent
  in
  aux env
;;

let lookup_env name (env : ('binding, 'obj) t) =
  match name with
  | Base n -> lookup_env_local n (fst env)
  | Namespaced (path, n) ->
  match Hashtbl.find_opt (snd env) path with
  | None -> None
  | Some mod_env ->
  match Hashtbl.find_opt mod_env n with
  | None -> None
  | Some obj -> Some obj
;;

let exists name env =
  match lookup_env name env with
  | None -> false
  | Some _ -> true
;;

let lookup_env_local_by_property (prop : 'obj -> bool) (env : ('binding, 'obj) env_local) =
  let rec aux env =
    match env with
    | Top -> None
    | Frame { parent; binding; obj } ->
      if prop obj then Some (binding, obj) else aux parent
  in
  aux env
;;

let lookup_env_by_property
      (path : string list)
      (prop : 'obj -> bool)
      (env : ('binding, 'obj) t)
  =
  match path with
  | [] -> lookup_env_local_by_property prop (fst env)
  | _ ->
  match Hashtbl.find_opt (snd env) path with
  | None -> None
  | Some (mod_env : ('binding, 'obj) env_module) ->
    (* search through the values in the hashtable to find a match *)
    Hashtbl.fold
      (fun binding obj acc ->
         match acc with
         | Some _ -> acc
         | None -> if prop obj then Some (binding, obj) else None)
      mod_env
      None
;;

let module_env_of_local_env (local_env : ('binding, 'obj) env_local)
  : ('binding, 'obj) env_module
  =
  let rec aux env acc =
    match env with
    | Top -> acc
    | Frame { parent; binding; obj } ->
      (* keep only the latest values *)
      if Hashtbl.mem acc binding
      then acc
      else (
        let new_acc =
          Hashtbl.add acc binding obj;
          acc
        in
        aux parent new_acc)
  in
  aux local_env (Hashtbl.create 16)
;;

let modularize_env ?(default = Top) (path : string list) (env : ('binding, 'obj) t)
  : ('binding, 'obj) t
  =
  if Hashtbl.mem (snd env) path
  then assert false (* make sure all paths are unique *)
  else (
    let local_env, module_env = env in
    let new_env_module = module_env_of_local_env local_env in
    Hashtbl.add module_env path new_env_module;
    default, module_env)
;;

let empty_env () : ('binding, 'obj) t = Top, Hashtbl.create 16

let fold_env f env acc =
  let rec fold_env_local env acc =
    match env with
    | Top -> acc
    | Frame { parent; binding; obj } -> fold_env_local parent (f binding obj acc)
  in
  fold_env_local (fst env) acc
;;
