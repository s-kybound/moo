module type JUDGEMENTS = sig
  val name : string

  (** the value judgement on producers *)
  val is_val : Ast.Core.producer -> bool

  (** the covalue judgement on consumers *)
  val is_coval : Ast.Core.consumer -> bool
end

module type EVALUATION_STRATEGY = sig
  (** a single step, corresponding to a step of small-step semantics *)
  type step =
    | Incomplete of Ast.Core.cut
    | Complete of Ast.Core.cut
    | Error of exn

  val name : string
  val step_once : Ast.Core.cut -> step

  (** steps a program through to completion within an environment *)
  val eval : Env.t -> Ast.Core.t -> Ast.Core.cut
end

module Eager : JUDGEMENTS
module Lazy : JUDGEMENTS
module Make_CBV : functor (_ : JUDGEMENTS) -> EVALUATION_STRATEGY
module Make_CBN : functor (_ : JUDGEMENTS) -> EVALUATION_STRATEGY
