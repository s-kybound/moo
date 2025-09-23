module Env : sig
  type t

  val empty_env : unit -> t
  val load_definitions : Ast.Core.t -> t -> unit
  val substitute_definitions : Ast.Core.cut -> t -> Ast.Core.cut
end

module type RUNNER = sig
  type step =
    | Incomplete of Ast.Core.cut
    | Complete of Ast.Core.cut
    | Error of exn

  val name : string
  val step_once : Ast.Core.cut -> step
  val eval : Env.t -> Ast.Core.t -> Ast.Core.cut
end

module Call_by_value : RUNNER
module Call_by_name : RUNNER
