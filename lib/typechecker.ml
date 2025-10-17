module type TYPECHECKER = sig
  val typecheck : Ast.Core.t -> (Ast.Core.t, exn) result
end

module Untyped : TYPECHECKER = struct
  let typecheck (ast : Ast.Core.t) : (Ast.Core.t, exn) result = Ok ast
end

module SimplyTyped : TYPECHECKER = struct
  let typecheck (_ast : Ast.Core.t) : (Ast.Core.t, exn) result =
    Error (Failure "simply-typed typechecker not implemented")
  ;;
end

module SystemF : TYPECHECKER = struct
  let typecheck (_ast : Ast.Core.t) : (Ast.Core.t, exn) result =
    Error (Failure "system-F typechecker not implemented")
  ;;
end

module HindleyMilner : TYPECHECKER = struct
  let typecheck (_ast : Ast.Core.t) : (Ast.Core.t, exn) result =
    Error (Failure "hindley-milner typechecker not implemented")
  ;;
end
