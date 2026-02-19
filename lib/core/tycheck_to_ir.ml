open Syntax

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

let gensym =
  let counter = ref 0 in
  fun prefix ->
    let name = Printf.sprintf "%s_%d" prefix !counter in
    incr counter;
    name
;;

let tycheck_binder_to_ir_binder (b : Typechecker.Bidir.tycheck_binder) : Ir.name =
  match b.original_binder with
  | Ast.Var name -> name
  | Ast.Wildcard -> gensym "wildcard"
;;

let tycheck_var_to_ir_name (v : Typechecker.Bidir.tycheck_var) : Ir.name =
  match v.original_name with
  | Base n -> n
  | Namespaced _ -> failwith "TODO: namespacing in typechecked AST to IR conversion"
;;

let tycheck_to_ir_form (f : Typechecker.Bidir.tycheck_pattern) : Ir.form =
  match f with
  | Typechecker.Bidir.TNumeral n -> Ir.Numeral n
  | Typechecker.Bidir.TPatVariable pb -> Ir.Binder (tycheck_binder_to_ir_binder pb)
  | Typechecker.Bidir.TTup names ->
    let names = List.map tycheck_binder_to_ir_binder names in
    Ir.Tuple names
  | Typechecker.Bidir.TConstr { tpat_name; tpat_args } ->
    Ir.Constr
      { form_name = ast_name_to_ir_name tpat_name
      ; form_args = List.map tycheck_binder_to_ir_binder tpat_args
      }
;;

let should_focus_left (tyu : Ast.ty_use) : bool =
  match tyu with
  | Ast.Polarised (pol, Ast.Raw (mode, _shape, _raw_ty)) ->
    (match pol, mode with
     | Plus, By_value | Minus, By_name -> true
     | Plus, By_name | Minus, By_value -> false)
  | _ -> true
;;

(* invariant: terms should be annotated with their types *)
let rec tycheck_to_ir_command (c : Typechecker.Bidir.tycheck_command) : Ir.command =
  match c with
  | Typechecker.Bidir.TCore { tl_term = Typechecker.Bidir.TAnn (l_term, l_tyu); tr_term }
    ->
    if should_focus_left l_tyu
    then
      Ir.Core
        { focus_term = tycheck_to_ir_term l_term
        ; unfocus_term = tycheck_to_ir_term tr_term
        }
    else
      Ir.Core
        { focus_term = tycheck_to_ir_term tr_term
        ; unfocus_term = tycheck_to_ir_term l_term
        }
  | Typechecker.Bidir.TCore { tl_term; tr_term } ->
    Ir.Core
      { focus_term = tycheck_to_ir_term tl_term
      ; unfocus_term = tycheck_to_ir_term tr_term
      }
  | Typechecker.Bidir.TArith (Typechecker.Bidir.TUnop { top; tin_term; tout_term }) ->
    Ir.Arith
      (Ir.Unop
         { op = tycheck_to_ir_unop top
         ; in_focus_term = tycheck_to_ir_term tin_term
         ; out_unfocus_term = tycheck_to_ir_term tout_term
         })
  | Typechecker.Bidir.TArith (Typechecker.Bidir.TBop { top; tl_term; tr_term; tout_term })
    ->
    Ir.Arith
      (Ir.Bop
         { op = tycheck_to_ir_bop top
         ; l_focus_term = tycheck_to_ir_term tl_term
         ; r_focus_term = tycheck_to_ir_term tr_term
         ; out_unfocus_term = tycheck_to_ir_term tout_term
         })
  | Typechecker.Bidir.TFork (c1, c2) ->
    Ir.Fork (tycheck_to_ir_command c1, tycheck_to_ir_command c2)

and tycheck_to_ir_term (t : Typechecker.Bidir.tycheck_term) : Ir.term =
  match t with
  | Typechecker.Bidir.TMu (name, command) ->
    Ir.Mu (tycheck_binder_to_ir_binder name, tycheck_to_ir_command command)
  | Typechecker.Bidir.TVariable name -> Ir.Variable (tycheck_var_to_ir_name name)
  | Typechecker.Bidir.TConstruction { tcons_name; tcons_args } ->
    Ir.Construction
      { cons_name = ast_name_to_ir_name tcons_name
      ; cons_args = List.map tycheck_to_ir_term tcons_args
      }
  | Typechecker.Bidir.TTuple terms -> Ir.Tuple (List.map tycheck_to_ir_term terms)
  | Typechecker.Bidir.TMatcher branches ->
    let ir_branches =
      List.map
        (fun (pat, command) ->
           let ir_form = tycheck_to_ir_form pat in
           let ir_command = tycheck_to_ir_command command in
           ir_form, ir_command)
        branches
    in
    Ir.Matcher ir_branches
  | Typechecker.Bidir.TNum n -> Ir.Num n
  | Typechecker.Bidir.TRec (name, term) ->
    Ir.Rec (tycheck_binder_to_ir_binder name, tycheck_to_ir_term term)
  | Typechecker.Bidir.TArr terms -> Ir.Arr (List.map tycheck_to_ir_term terms)
  | Typechecker.Bidir.TAnn (term, _) -> tycheck_to_ir_term term
  | Typechecker.Bidir.TDone -> Ir.Done
;;

let empty_tycheck_command : Typechecker.Bidir.tycheck_command =
  Typechecker.Bidir.TCore
    { tl_term =
        Typechecker.Bidir.TAnn
          ( Typechecker.Bidir.TDone
          , Ast.Polarised (Ast.Plus, Ast.Raw (Ast.By_value, Ast.Data, Ast.Product [])) )
    ; tr_term = Typechecker.Bidir.TTuple []
    }
;;

(* a sequential order of commands to do by the program *)
let tycheck_command_of_module ((defs, cmd) : Typechecker.Bidir.tycheck_module)
  : Typechecker.Bidir.tycheck_command
  =
  let base =
    match cmd with
    | Some new_base -> new_base
    | None -> empty_tycheck_command
  in
  let rec aux (defs : Typechecker.Bidir.tycheck_top_level_item list) end_cmd
    : Typechecker.Bidir.tycheck_command
    =
    match defs with
    | [] -> end_cmd
    | Typechecker.Bidir.Open _ :: rest -> aux rest end_cmd
    | Typechecker.Bidir.Def (Typechecker.Bidir.TTypeDef (_kind_binder, _ty_def)) :: rest
      -> aux rest end_cmd
    | Typechecker.Bidir.Def (Typechecker.Bidir.TModuleDef _) :: _ ->
      failwith "Nested modules not supported in typechecked AST to IR conversion"
    | Typechecker.Bidir.Def (Typechecker.Bidir.TTermDef (b, term)) :: rest ->
      let rest_cmd = aux rest end_cmd in
      Typechecker.Bidir.TCore
        { tl_term = term; tr_term = Typechecker.Bidir.TMu (b, rest_cmd) }
  in
  aux defs base
;;
