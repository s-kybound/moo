type 'ann resolved = Resolved of 'ann Syntax.Ast.module_

(** Resolves all module usages in the given module. *)
val replace_module : 'ann Syntax.Ast.module_ -> 'ann resolved
