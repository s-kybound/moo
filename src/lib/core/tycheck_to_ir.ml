open Syntax
open Typechecker.Ty_ast

let tycheck_to_ir_unop (op : Ast.unop) : Ir.unop =
  match op with
  | Ast.Neg -> Ir.Neg
  | Ast.Not -> Ir.Not
;;

let tycheck_to_ir_bop (op : Ast.bop) : Ir.bop =
  match op with
  | Ast.Add -> Ir.Add
  | Ast.Sub -> Ir.Sub
  | Ast.Mul -> Ir.Mul
  | Ast.Div -> Ir.Div
  | Ast.Mod -> Ir.Mod
  | Ast.And -> Ir.And
  | Ast.Or -> Ir.Or
  | Ast.Xor -> Ir.Xor
  | Ast.Shl -> Ir.Shl
  | Ast.Shr -> Ir.Shr
;;

let strip_namespacing (n : Ast.name) : string =
  match n with
  | Base n -> n
  | Namespaced (_, n) -> n
;;

let binder_to_ir_name (b : typed_binder) : Ir.name =
  match b with
  | Ast.Var (_ann, name) -> Var name
  | Ast.Wildcard _ann -> Wildcard
;;

let tycheck_to_ir_form (f : typed_pattern) : Ir.form =
  match f with
  | Ast.Numeral n -> Ir.Numeral n
  | Ast.Binder pb -> Ir.Binder (binder_to_ir_name pb)
  | Ast.Tup names -> Ir.Tuple (List.map binder_to_ir_name names)
  | Ast.Constr { pat_name; pat_args } ->
    Ir.Constr
      { form_name = strip_namespacing pat_name
      ; form_args = List.map binder_to_ir_name pat_args
      }
;;

let rec should_focus_left (tyu : Ast.ty_use) (tydef_env : Type.tydef_env) : bool =
  match tyu with
  | Ast.Polarised (pol, ty) ->
    let mode, _, _ = Type.ty_to_raw_ty ty tydef_env in
    begin match pol, mode with
    | Plus, By_value | Minus, By_name -> true
    | Plus, By_name | Minus, By_value -> false
    end
  | Ast.AbstractIntroducer (_, tyu) -> should_focus_left tyu tydef_env
  | Ast.Abstract _ -> failwith "TODO: abstract types not supported yet"
  | Ast.Weak { link = { negated; meta } } ->
  match meta.cell with
  | Unified tyu -> should_focus_left tyu tydef_env <> negated
  | Inferred { constructor = Some cons; _ } -> cons <> negated
  | Inferred { constructor = None; _ } ->
    let message =
      Printf.sprintf
        "Weak type variable ?%d is underspecified, cannot determine focus direction"
        meta.id
    in
    raise (Error.TypeError { loc = None; message })
;;

let term_focuses_left (t : typed_term) (tydef_env : Type.tydef_env) : bool =
  let ann, _ = t in
  match ann.ty with
  | Some tyu -> should_focus_left tyu tydef_env
  | None ->
    let message =
      Printf.sprintf
        "Term %s does not have a type annotation, cannot determine focus direction"
        (Pretty.show_term ~ann_show:(fun _ s -> s) t)
    in
    raise (Error.TypeError { loc = ann.loc; message })
;;

let rec tycheck_to_ir_command tydef_env (c : typed_command) : Ir.command =
  let _ann, node = c in
  match node with
  | Ast.Core { l_term; r_term } ->
    if term_focuses_left l_term tydef_env
    then
      Ir.Core
        { focus_term = tycheck_to_ir_term tydef_env l_term
        ; unfocus_term = tycheck_to_ir_term tydef_env r_term
        }
    else
      Ir.Core
        { focus_term = tycheck_to_ir_term tydef_env r_term
        ; unfocus_term = tycheck_to_ir_term tydef_env l_term
        }
  | Ast.Arith (Ast.Unop { out_term; _ } as a) | Ast.Arith (Ast.Bop { out_term; _ } as a)
    ->
    let left_focus = not (term_focuses_left out_term tydef_env) in
    begin match a with
    | Ast.Unop { op; in_term; out_term } ->
      Ir.Arith
        (Ir.Unop
           { op = tycheck_to_ir_unop op
           ; in_term = tycheck_to_ir_term tydef_env in_term
           ; out_term = tycheck_to_ir_term tydef_env out_term
           ; left_focus
           })
    | Ast.Bop { op; l_term; r_term; out_term } ->
      Ir.Arith
        (Ir.Bop
           { op = tycheck_to_ir_bop op
           ; l_focus_term = tycheck_to_ir_term tydef_env l_term
           ; r_focus_term = tycheck_to_ir_term tydef_env r_term
           ; out_term = tycheck_to_ir_term tydef_env out_term
           ; left_focus
           })
    end
  | Ast.Fork (c1, c2) ->
    Ir.Fork (tycheck_to_ir_command tydef_env c1, tycheck_to_ir_command tydef_env c2)

and tycheck_to_ir_term tydef_env (t : typed_term) : Ir.term =
  let _ann, node = t in
  let new_t =
    match node with
    | Ast.Mu (name, command) ->
      Ir.Mu (binder_to_ir_name name, tycheck_to_ir_command tydef_env command)
    | Ast.Variable name -> Ir.Variable name
    | Ast.Construction { cons_name; cons_args } ->
      Ir.Construction
        { cons_name = strip_namespacing cons_name
        ; cons_args = List.map (tycheck_to_ir_term tydef_env) cons_args
        }
    | Ast.Tuple terms -> Ir.Tuple (List.map (tycheck_to_ir_term tydef_env) terms)
    | Ast.Matcher branches ->
      let ir_branches =
        List.map
          (fun (pat, command) ->
             let ir_form = tycheck_to_ir_form pat in
             let ir_command = tycheck_to_ir_command tydef_env command in
             ir_form, ir_command)
          branches
      in
      Ir.Matcher ir_branches
    | Ast.Num n -> Ir.Num n
    | Ast.Rec (Ast.Wildcard _, _) ->
      assert false (* wildcard binders are not allowed in rec terms *)
    | Ast.Rec (Ast.Var (_, name), term) -> Ir.Rec (name, tycheck_to_ir_term tydef_env term)
    | Ast.Arr terms -> Ir.Arr (List.map (tycheck_to_ir_term tydef_env) terms)
    | Ast.Ann (term, _) -> tycheck_to_ir_term tydef_env term
    | Ast.Exit -> Ir.Exit
  in
  if term_focuses_left t tydef_env then Ir.NeedsForce new_t else new_t
;;

let tycheck_command_of_module
      (type_context : Typechecker.Bidir.module_type_context)
      (defs : typed_module)
  : Ir.command
  =
  let rec aux (defs : typed_mod_tli Ast.top_level_item list) end_cmd : Ir.command =
    match defs with
    | [] -> end_cmd
    | Ast.Open _ :: rest -> aux rest end_cmd
    | Ast.Def (Ast.TypeDef _) :: rest -> aux rest end_cmd
    | Ast.Def (Ast.TermDef (b, term)) :: rest ->
      let rest_cmd = aux rest end_cmd in
      let t = tycheck_to_ir_term type_context.tydef_env term in
      let rest_mu = Ir.Mu (binder_to_ir_name b, rest_cmd) in
      if term_focuses_left term type_context.tydef_env
      then Ir.Core { focus_term = t; unfocus_term = rest_mu }
      else Ir.Core { focus_term = rest_mu; unfocus_term = t }
    | Ast.Def (Ast.Term term) :: rest ->
      let rest_cmd = aux rest end_cmd in
      let t = tycheck_to_ir_term type_context.tydef_env term in
      let rest_mu = Ir.Mu (Wildcard, rest_cmd) in
      if term_focuses_left term type_context.tydef_env
      then Ir.Core { focus_term = t; unfocus_term = rest_mu }
      else Ir.Core { focus_term = rest_mu; unfocus_term = t }
  in
  aux defs ModEndHole
;;
