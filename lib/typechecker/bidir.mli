open Syntax

(**
 * Given a program and an initial type definition environment, return a typechecked program
 * and an updated type definition environment.
 *)
val tycheck_program
  :  Ast.core_ann Ast.module_
  -> Type.tydef_env
  -> Ty_ast.typed_module * Type.tydef_env
