open Syntax
open Converter

type module_type_context =
  { hole_env : tycheck_hole_environment_frame
  ; ty_env : Type.ty_env
  ; tydef_env : Type.tydef_env
  }

val empty_type_context : module_type_context

(**
 * Given a program and an initial type definition environment, return a typechecked program
 * and an updated type definition environment.
 *)
val tycheck_program
  :  Ast.core_ann Ast.module_
  -> module_type_context
  -> Ty_ast.typed_module * module_type_context
