type t

val empty_env : unit -> t
val has_term : t -> string -> bool
val has_type : t -> string -> bool

val get_type
  :  t
  -> string
  -> (Ast.Core.Type.type_schema * Ast.Core.Type.type_expr, exn) result

val load_definitions : Ast.Core.t -> t -> unit
val substitute_definitions : Ast.Core.cut -> t -> Ast.Core.cut
