module type RUNNER = sig
  type step =
    | Incomplete of Ast.Core.t
    | Complete of Ast.Core.t
    | Error of exn

  val step_once : Ast.Core.t -> step
  val eval : Ast.Core.t -> Ast.Core.t
end

module Call_by_value : RUNNER
module Call_by_name : RUNNER
