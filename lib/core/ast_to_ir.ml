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

let ast_to_ir_form (f : Ast.pattern) : Ir.form =
  let pat_binder_to_name pb =
    match pb with
    | Ast.Var { name; typ = _ } -> name
    | Ast.Wildcard -> gensym "wildcard"
  in
  match f with
  | Ast.Pat_binder pb ->
    Ir.Binder (pat_binder_to_name pb)
  | Ast.Tup names ->
    let names = List.map pat_binder_to_name names in
    Ir.Tuple names
  | Ast.Constr { pat_name; pat_args } ->
    Ir.Constr
      { form_name = ast_name_to_ir_name pat_name
      ; form_args = List.map pat_binder_to_name pat_args
      }
;;

(* invariant: terms should be annotated with their types *)
let rec ast_to_ir_command (c : Ast.command) : Ir.command =
  match c with
  | Ast.Core { l_term = Ast.Ann (l_term, Polarised (pol, (Some mode, _))); r_term } ->
    (match pol, mode with
     (* left term eagerly captures right term *)
     | Plus, By_value | Minus, By_name ->
       Ir.Core
         { focus_term = ast_to_ir_term l_term; unfocus_term = ast_to_ir_term r_term }
     (* right term eagerly captures left term *)
     | Plus, By_name | Minus, By_value ->
       Ir.Core
         { focus_term = ast_to_ir_term r_term; unfocus_term = ast_to_ir_term l_term })
  | Ast.Core _ -> failwith "Only annotated left terms are supported in Core commands"
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
  | Ast.Mu ({ name; typ = _ }, command) -> Ir.Mu (name, ast_to_ir_command command)
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
  | Ast.Rec ({ name; typ = _ }, term) -> Ir.Rec (name, ast_to_ir_term term)
  | Ast.Arr terms -> Ir.Arr (List.map ast_to_ir_term terms)
  | Ast.Ann (term, _) -> ast_to_ir_term term
  | Ast.Done -> Ir.Done
;;

let empty_ast_command : Ast.command =
  Ast.Core
    { l_term =
        Ast.Ann
          ( Ast.Done
          , Ast.Polarised (Ast.Plus, (Some Ast.By_value, Ast.Raw (Ast.Data, Ast.Raw64)))
          )
    ; r_term = Ast.Done
    }
;;

let ast_command_of_module (m : Ast.module_) : Ast.command =
  let base =
    match m.command with
    | Some cmd -> cmd
    | None -> empty_ast_command
  in
  let rec aux (defs : Ast.definition list) end_cmd : Ast.command =
    match defs with
    | [] -> end_cmd
    | TypeDef (_kind_binder, _ty_def) :: rest ->
      aux rest end_cmd
    | ModuleDef _ :: _ ->
      failwith "Nested modules not supported in AST to IR conversion"
    | TermDef (b, term) :: rest ->
      let rest_cmd = aux rest end_cmd in
      Core {
        l_term = term;
        r_term = Mu (b, rest_cmd);
      }
  in
  aux m.definitions base
;;
