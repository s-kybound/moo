open Syntax

let ast_to_ir_unop (op : Ast.unop) : Ir.unop =
  match op with
  | Ast.Neg -> Ir.Neg
  | Ast.Not -> Ir.Not
;;

let ast_to_ir_bop (op : Ast.bop) : Ir.bop =
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
  | Namespaced _ -> failwith "TODO: namespacing in AST to IR conversion"
;;

let gensym =
  let counter = ref 0 in
  fun prefix ->
    let name = Printf.sprintf "%s_%d" prefix !counter in
    incr counter;
    name
;;

let ast_binder_to_ir_binder (b : Ast.binder) : Ir.name =
  match b with
  | Var name -> name
  | Wildcard -> gensym "wildcard"
;;

let ast_to_ir_form (f : Ast.pattern) : Ir.form =
  match f with
  | Ast.Numeral n -> Ir.Numeral n
  | Ast.Binder pb -> Ir.Binder (ast_binder_to_ir_binder pb)
  | Ast.Tup names ->
    let names = List.map ast_binder_to_ir_binder names in
    Ir.Tuple names
  | Ast.Constr { pat_name; pat_args } ->
    Ir.Constr
      { form_name = ast_name_to_ir_name pat_name
      ; form_args = List.map ast_binder_to_ir_binder pat_args
      }
;;

(* invariant: terms should be annotated with their types *)
let rec ast_to_ir_command (c : Ast.command) : Ir.command =
  match c with
  (* | Ast.Core { l_term = Ast.Ann (l_term, Polarised (pol, (Some mode, _))); r_term } ->
    (match pol, mode with
     (* left term eagerly captures right term *)
     | Plus, By_value | Minus, By_name ->
       Ir.Core
         { focus_term = ast_to_ir_term l_term; unfocus_term = ast_to_ir_term r_term }
     (* right term eagerly captures left term *)
     | Plus, By_name | Minus, By_value ->
       Ir.Core
         { focus_term = ast_to_ir_term r_term; unfocus_term = ast_to_ir_term l_term }) *)
  | Ast.Core _ ->
    failwith
      "need to convert to the typechecked AST first to get the annotations for Core \
       commands"
  | Ast.Arith (Ast.Unop { op; in_term; out_term }) ->
    Ir.Arith
      (Ir.Unop
         { op = ast_to_ir_unop op
         ; in_focus_term = ast_to_ir_term in_term
         ; out_unfocus_term = ast_to_ir_term out_term
         })
  | Ast.Arith (Ast.Bop { op; l_term; r_term; out_term }) ->
    Ir.Arith
      (Ir.Bop
         { op = ast_to_ir_bop op
         ; l_focus_term = ast_to_ir_term l_term
         ; r_focus_term = ast_to_ir_term r_term
         ; out_unfocus_term = ast_to_ir_term out_term
         })
  | Ast.Fork (c1, c2) -> Ir.Fork (ast_to_ir_command c1, ast_to_ir_command c2)

and ast_to_ir_term (t : Ast.term) : Ir.term =
  match t with
  | Ast.Mu (name, command) ->
    Ir.Mu (ast_binder_to_ir_binder name, ast_to_ir_command command)
  | Ast.Variable name -> Ir.Variable (ast_name_to_ir_name name)
  | Ast.Construction { cons_name; cons_args } ->
    Ir.Construction
      { cons_name = ast_name_to_ir_name cons_name
      ; cons_args = List.map ast_to_ir_term cons_args
      }
  | Ast.Tuple terms -> Ir.Tuple (List.map ast_to_ir_term terms)
  | Ast.Matcher branches ->
    let ir_branches =
      List.map
        (fun (pat, command) ->
           let ir_form = ast_to_ir_form pat in
           let ir_command = ast_to_ir_command command in
           ir_form, ir_command)
        branches
    in
    Ir.Matcher ir_branches
  | Ast.Num n -> Ir.Num n
  | Ast.Rec (name, term) -> Ir.Rec (ast_binder_to_ir_binder name, ast_to_ir_term term)
  | Ast.Arr terms -> Ir.Arr (List.map ast_to_ir_term terms)
  | Ast.Ann (term, _) -> ast_to_ir_term term
  | Ast.Done -> Ir.Done
;;

let empty_ast_command : Ast.command =
  Ast.Core
    { l_term =
        Ast.Ann
          ( Ast.Done
          , Ast.Polarised (Ast.Plus, Ast.Raw (Ast.By_value, Ast.Data, Ast.Product [])) )
    ; r_term = Ast.Tuple []
    }
;;

(* a sequential order of commands to do by the program *)
let ast_command_of_module ((defs, cmd) : Ast.module_) : Ast.command =
  let base =
    match cmd with
    | Some new_base -> new_base
    | None -> empty_ast_command
  in
  let rec aux (defs : Ast.definition Ast.top_level_item list) end_cmd : Ast.command =
    match defs with
    | [] -> end_cmd
    | Open _ :: rest -> aux rest end_cmd
    | Def (TypeDef (_kind_binder, _ty_def)) :: rest -> aux rest end_cmd
    | Def (ModuleDef _) :: _ ->
      failwith "Nested modules not supported in AST to IR conversion"
    | Def (TermDef (b, term)) :: rest ->
      let rest_cmd = aux rest end_cmd in
      Core { l_term = term; r_term = Mu (b, rest_cmd) }
  in
  aux defs base
;;
