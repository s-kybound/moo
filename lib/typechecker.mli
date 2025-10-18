exception TypeError of (string * Lexing.position) list

module TypeSubstituter : sig
  val substitute_type_expr
    :  kind_params:Ast.Core.Type.type_use list
    -> kind_body:Ast.Core.Type.type_expr
    -> Ast.Core.Type.type_expr

  val simplify_type_use : Env.t -> Ast.Core.Type.type_use -> Ast.Core.Type.type_use
end

module type TYPECHECKER = sig
  val typecheck : Ast.Core.t -> (Ast.Core.t, exn) result
end

module Untyped : TYPECHECKER
module SimplyTyped : TYPECHECKER
module SystemF : TYPECHECKER
module HindleyMilner : TYPECHECKER
