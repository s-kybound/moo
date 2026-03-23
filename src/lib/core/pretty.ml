open Ir

let show_unop op =
  match op with
  | Neg -> "-"
  | Not -> "!"
;;

let show_bop op =
  match op with
  | Add -> "+"
  | Sub -> "-"
  | Mul -> "*"
  | Div -> "/"
  | Mod -> "%"
  | And -> "&"
  | Or -> "|"
  | Xor -> "^"
  | Shl -> "<<"
  | Shr -> ">>"
;;

let show_name name =
  match name with
  | Var s -> s
  | Wildcard -> "_"
;;

let show_form form =
  match form with
  | Binder name -> show_name name
  | Tuple [ name ] -> Printf.sprintf "(%s,)" (show_name name)
  | Tuple names -> "(" ^ String.concat ", " (List.map show_name names) ^ ")"
  | Constr { form_name; form_args } ->
    Printf.sprintf "%s(%s)" form_name (String.concat ", " (List.map show_name form_args))
  | Numeral n -> Int64.to_string n
;;

let rec show_term term =
  match term with
  | NeedsForce t -> Printf.sprintf "force(%s)" (show_term t)
  | Mu (name, cmd) -> Printf.sprintf "mu{ %s. %s }" (show_name name) (show_command cmd)
  | Variable name -> Syntax.Pretty.show_name name
  | Construction { cons_name; cons_args } ->
    Printf.sprintf "%s(%s)" cons_name (String.concat ", " (List.map show_term cons_args))
  | Tuple [ term ] -> Printf.sprintf "(%s,)" (show_term term)
  | Tuple terms -> Printf.sprintf "(%s)" (String.concat ", " (List.map show_term terms))
  | Matcher branches ->
    let branch_strs =
      List.map
        (fun (form, cmd) ->
           Printf.sprintf "| %s -> %s" (show_form form) (show_command cmd))
        branches
    in
    "match { " ^ String.concat " " branch_strs ^ " }"
  | Num n -> Int64.to_string n
  | Rec (name, t) -> Printf.sprintf "[rec %s] %s" name (show_term t)
  | Arr terms -> Printf.sprintf "[%s]" (String.concat ", " (List.map show_term terms))
  | Val v -> show_value v
  | Exit -> "exit"

and show_command command =
  match command with
  | Core { focus_term; unfocus_term } ->
    Printf.sprintf "%s >> %s" (show_term focus_term) (show_term unfocus_term)
  | Arith (Unop { op; in_term; out_term; left_focus }) ->
    let direction = if left_focus then ">>" else "<<" in
    Printf.sprintf
      "%s(%s %s %s)"
      (show_unop op)
      (show_term in_term)
      direction
      (show_term out_term)
  | Arith (Bop { op; l_focus_term; r_focus_term; out_term; left_focus }) ->
    let direction = if left_focus then ">>" else "<<" in
    Printf.sprintf
      "%s(%s, %s %s %s)"
      (show_bop op)
      (show_term l_focus_term)
      (show_term r_focus_term)
      direction
      (show_term out_term)
  | Fork (cmd1, cmd2) ->
    Printf.sprintf "[%s | %s]" (show_command cmd1) (show_command cmd2)
  | ModEndHole -> "MOD_END_HOLE"

and show_instruction instr =
  match instr with
  | Force -> "FORCE"
  | Cut -> "CUT"
  | Con_instr (cons_name, arity) -> Printf.sprintf "CONS(%s, %d)" cons_name arity
  | Spawn cmd -> Printf.sprintf "SPAWN(%s)" (show_command cmd)
  | Tup_instr arity -> Printf.sprintf "TUP(%d)" arity
  | Arr_instr arity -> Printf.sprintf "ARR(%d)" arity
  | Unop_instr op -> Printf.sprintf "UNOP(%s)" (show_unop op)
  | Bop_instr op -> Printf.sprintf "BOP(%s)" (show_bop op)
  | Set_instr name -> Printf.sprintf "SET(%s)" name
  | Exit_env -> "EXIT_ENV"

and show_control_item ci =
  match ci with
  | I instr -> "I: " ^ show_instruction instr
  | T term -> "T: " ^ show_term term
  | C cmd -> "C: " ^ show_command cmd

and show_value v =
  match v with
  | VMu (name, _, _, _) -> Printf.sprintf "<mu %s>" (show_name name)
  | VConstruction (name, args) ->
    let args_str = String.concat ", " (List.map show_value args) in
    Printf.sprintf "%s(%s)" name args_str
  | VTuple args ->
    let args_str = String.concat ", " (List.map show_value args) in
    Printf.sprintf "(%s)" args_str
  | VArr arr ->
    let args_str = String.concat ", " (Array.to_list arr |> List.map show_value) in
    Printf.sprintf "[%s]" args_str
  | VMatcher _ -> "<match>"
  | VNum n -> Int64.to_string n
  | VExit -> "exit"
  | VHole -> "<hole>"
;;
