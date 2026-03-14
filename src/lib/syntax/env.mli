(**
 * A resolved value in the environment, which includes its origin path and the actual object.
 *)
type 'obj resolved =
  { origin_path : string list
  ; obj : 'obj
  }

(**
 * Environment type. A stack of frames and a module environment mapping
 *)
type 'obj t

(** 
 * Extend the environment with a new binding. The new binding is added to the top frame.
 *)
val extend_env : string -> 'obj -> 'obj t -> 'obj t

(** 
 * Exit the current frame and return the parent environment.
 *)
val exit_env : 'obj t -> 'obj t option

(**
 * Look up a value in the environment by its name.
 *)
val lookup_env : Surface.name -> 'obj t -> 'obj resolved option

(**
 * Check if a name exists in the environment.
 *)
val exists : Surface.name -> 'obj t -> bool

(**
 * Look up a value in the environment by its name, returning its origin path as well.
 *)
val lookup_env_by_property
  :  string list
  -> ('obj -> bool)
  -> 'obj t
  -> (string * 'obj resolved) option

(**
 * Convert the local environment into a module environment.
 * To be used at the end of a module, when we want to export its bindings to be used by other modules.
 *)
val modularize_env : string list -> 'obj t -> 'obj t

val empty_env : unit -> 'obj t

(**
 * Fold over the local environment.
 *)
val fold_env : (string -> 'obj -> 'acc -> 'acc) -> 'obj t -> 'acc -> 'acc
