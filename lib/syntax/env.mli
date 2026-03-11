type 'obj resolved =
  { origin_path : string list
  ; obj : 'obj
  }

type 'obj t

val extend_env : string -> 'obj -> 'obj t -> 'obj t
val exit_env : 'obj t -> 'obj t option
val lookup_env : Surface.name -> 'obj t -> 'obj resolved option
val exists : Surface.name -> 'obj t -> bool

val lookup_env_by_property
  :  string list
  -> ('obj -> bool)
  -> 'obj t
  -> (string * 'obj resolved) option

val modularize_env : string list -> 'obj t -> 'obj t
val empty_env : unit -> 'obj t
val fold_env : (string -> 'obj -> 'acc -> 'acc) -> 'obj t -> 'acc -> 'acc
