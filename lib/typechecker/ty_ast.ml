open Syntax

type tycheck_ann =
  { loc : Loc.span option
  ; ty : Ast.ty_use option
  ; unique_id : int option
  ; binder_ids : int list option
  }

type typed_ann = tycheck_ann
type typed_binder = typed_ann Ast.binder
type typed_pattern = typed_ann Ast.pattern
type typed_term = typed_ann Ast.term
type typed_command = typed_ann Ast.command
type typed_arith_command = typed_ann Ast.arith_command
type typed_mod_tli = typed_ann Ast.mod_tli
type typed_module = typed_ann Ast.module_
