open Syntax
open Typechecker.Bidir
open Utils.Fresh

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

let ast_name_to_ir_name (n : Ast.name) : Ir.name =
  match n with
  | Base n -> n
  | Namespaced _ -> failwith "TODO: namespacing in typechecked AST to IR conversion"
;;

let binder_to_ir_name (b : typed_binder) : Ir.name =
  match b with
  | Ast.Var (_ann, name) -> name
  | Ast.Wildcard _ann -> genvar "wildcard"
;;

let tycheck_to_ir_form (f : typed_pattern) : Ir.form =
  match f with
  | Ast.Numeral n -> Ir.Numeral n
  | Ast.Binder pb -> Ir.Binder (binder_to_ir_name pb)
  | Ast.Tup names -> Ir.Tuple (List.map binder_to_ir_name names)
  | Ast.Constr { pat_name; pat_args } ->
    Ir.Constr
      { form_name = ast_name_to_ir_name pat_name
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
  | Ast.Weak { negated; meta } ->
  match meta.cell with
  | Unified tyu -> should_focus_left tyu tydef_env <> negated
  | Inferred { constructor = Some cons; _ } -> cons <> negated
  | Inferred { constructor = None; _ } -> assert false
;;

let rec tycheck_to_ir_command tydef_env (c : typed_command) : Ir.command =
  let _ann, node = c in
  match node with
  | Ast.Core { l_term; r_term } ->
    let focus_left =
      let l_ann, _ = l_term in
      match l_ann.ty with
      | Some tyu -> should_focus_left tyu tydef_env
      | None -> assert false
    in
    if focus_left
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
  | Ast.Arith (Ast.Unop { op = top; in_term = tin_term; out_term = tout_term }) ->
    Ir.Arith
      (Ir.Unop
         { op = tycheck_to_ir_unop top
         ; in_focus_term = tycheck_to_ir_term tydef_env tin_term
         ; out_unfocus_term = tycheck_to_ir_term tydef_env tout_term
         })
  | Ast.Arith
      (Ast.Bop { op = top; l_term = tl_term; r_term = tr_term; out_term = tout_term }) ->
    Ir.Arith
      (Ir.Bop
         { op = tycheck_to_ir_bop top
         ; l_focus_term = tycheck_to_ir_term tydef_env tl_term
         ; r_focus_term = tycheck_to_ir_term tydef_env tr_term
         ; out_unfocus_term = tycheck_to_ir_term tydef_env tout_term
         })
  | Ast.Fork (c1, c2) ->
    Ir.Fork (tycheck_to_ir_command tydef_env c1, tycheck_to_ir_command tydef_env c2)

and tycheck_to_ir_term tydef_env (t : typed_term) : Ir.term =
  let ann, node = t in
  let t =
    match node with
    | Ast.Mu (name, command) ->
      Ir.Mu (binder_to_ir_name name, tycheck_to_ir_command tydef_env command)
    | Ast.Variable name -> Ir.Variable (ast_name_to_ir_name name)
    | Ast.Construction { cons_name; cons_args } ->
      Ir.Construction
        { cons_name = ast_name_to_ir_name cons_name
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
    | Ast.Rec (name, term) ->
      Ir.Rec (binder_to_ir_name name, tycheck_to_ir_term tydef_env term)
    | Ast.Arr terms -> Ir.Arr (List.map (tycheck_to_ir_term tydef_env) terms)
    | Ast.Ann (term, _) -> tycheck_to_ir_term tydef_env term
    | Ast.Exit -> Ir.Exit
  in
  match ann.ty with
  | Some tyu -> if should_focus_left tyu tydef_env then Ir.NeedsForce t else t
  | None -> assert false
;;

let tycheck_command_of_module tydef_env (defs : typed_module) : Ir.command =
  let rec aux (defs : typed_mod_tli Ast.top_level_item list) end_cmd : Ir.command =
    match defs with
    | [] -> end_cmd
    | Ast.Open _ :: rest -> aux rest end_cmd
    | Ast.Def (Ast.TypeDef _) :: rest -> aux rest end_cmd
    | Ast.Def (Ast.TermDef (b, term)) :: rest ->
      let rest_cmd = aux rest end_cmd in
      let ann, _ = term in
      let t = tycheck_to_ir_term tydef_env term in
      let rest_mu = Ir.Mu (binder_to_ir_name b, rest_cmd) in
      let term_evaluated_left =
        match ann.ty with
        | Some tyu -> should_focus_left tyu tydef_env
        | None -> assert false
      in
      if term_evaluated_left
      then Ir.Core { focus_term = t; unfocus_term = rest_mu }
      else Ir.Core { focus_term = rest_mu; unfocus_term = t }
    | Ast.Def (Ast.Term term) :: rest ->
      let rest_cmd = aux rest end_cmd in
      let ann, _ = term in
      let t = tycheck_to_ir_term tydef_env term in
      let rest_mu = Ir.Mu (genvar "toplevel", rest_cmd) in
      let term_evaluated_left =
        match ann.ty with
        | Some tyu -> should_focus_left tyu tydef_env
        | _ -> assert false
      in
      if term_evaluated_left
      then Ir.Core { focus_term = t; unfocus_term = rest_mu }
      else Ir.Core { focus_term = rest_mu; unfocus_term = t }
  in
  aux defs ModEndHole
;;
