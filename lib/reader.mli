(* The parsing frontend of moo. *)

val of_channel : filename:string -> in_channel -> Ast.Surface.t
val of_string : ?filename:string -> string -> Ast.Surface.t
val of_file : string -> Ast.Surface.t
