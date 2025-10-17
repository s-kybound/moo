module type TYPECHECKER = sig
  val typecheck : Ast.Core.t -> (Ast.Core.t, exn) result
end

module Untyped : TYPECHECKER
module SimplyTyped : TYPECHECKER
module SystemF : TYPECHECKER
module HindleyMilner : TYPECHECKER
