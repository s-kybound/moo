open Ast

let rec show_name name =
  match name with
  | Namespaced { namespace; inner } -> Printf.sprintf "%s::%s" namespace (show_name inner)
  | Base s -> s
;;

let show_unop op =
  match op with
  | Not -> "!"
  | Neg -> "-"
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

let show_polarity p =
  match p with
  | Plus -> "+"
  | Minus -> "-"
;;

let show_mode m =
  match m with
  | By_value -> "cbv"
  | By_name -> "cbn"
;;

let show_shape s =
  match s with
  | Data -> "data"
  | Codata -> "codata"
;;

let rec show_ty_use tyu =
  match tyu with
  | Polarised (pol, m) -> Printf.sprintf "%s%s" (show_polarity pol) (show_moded_ty m)
  | Abstract { negated; name } -> if negated then Printf.sprintf "~%s" name else name
  | Unresolved raw -> Printf.sprintf "unresolved(%s)" (show_raw_ty raw)

and show_moded_ty (mode_opt, ty) =
  match mode_opt with
  | Some m -> Printf.sprintf "[%s]%s" (show_mode m) (show_ty ty)
  | None -> Printf.sprintf "[???]%s" (show_ty ty)

and show_ty ty =
  match ty with
  | Named (name, []) -> show_name name
  | Named (name, params) ->
    let params_str = params |> List.map show_ty_use |> String.concat ", " in
    Printf.sprintf "%s<%s>" (show_name name) params_str
  | Raw (shape, raw) -> Printf.sprintf "%s %s" (show_shape shape) (show_raw_ty raw)

and show_raw_ty raw =
  match raw with
  | Raw64 -> "raw64"
  | Unit -> "unit"
  | Product tys ->
    let tys_str = tys |> List.map show_ty_use |> String.concat ", " in
    Printf.sprintf "(%s)" tys_str
  | ADT variants ->
    let variants_str = variants |> List.map show_variant |> String.concat " | " in
    Printf.sprintf "{ %s }" variants_str
  | Array tyu -> Printf.sprintf "[%s]" (show_ty_use tyu)
  | Pattern variant -> show_variant variant

and show_variant (name, params) =
  let params_str = params |> List.map show_ty_use |> String.concat ", " in
  Printf.sprintf "%s(%s)" name params_str
;;

let show_kind_binder (name, params) =
  match params with
  | [] -> name
  | _ ->
    let params_str = String.concat ", " params in
    Printf.sprintf "%s<%s>" name params_str
;;

let show_binder binder =
  match binder.typ with
  | Some tyu -> Printf.sprintf "%s:%s" binder.name (show_ty_use tyu)
  | None -> binder.name
;;

let show_pattern pat =
  let show_pattern_binder pb =
    match pb with
    | Wildcard -> "_"
    | Var binder -> show_binder binder
  in
  match pat with
  | Pat_binder pb -> show_pattern_binder pb
  | Constr { pat_name; pat_args } ->
    let args_str = pat_args |> List.map show_pattern_binder |> String.concat ", " in
    Printf.sprintf "%s(%s)" (show_name pat_name) args_str
  | Tup pats ->
    let pats_str = pats |> List.map show_pattern_binder |> String.concat ", " in
    Printf.sprintf "(%s)" pats_str
;;

let rec show_term term =
  match term with
  | Mu (binder, cmd) ->
    Printf.sprintf "{ %s -> %s }" (show_binder binder) (show_command cmd)
  | Variable name -> show_name name
  | Construction { cons_name; cons_args } ->
    let args_str = cons_args |> List.map show_term |> String.concat ", " in
    Printf.sprintf "%s(%s)" (show_name cons_name) args_str
  | Tuple terms ->
    let terms_str = terms |> List.map show_term |> String.concat ", " in
    Printf.sprintf "(%s)" terms_str
  | Matcher arms ->
    let show_arm (pat, cmd) =
      Printf.sprintf "%s -> %s" (show_pattern pat) (show_command cmd)
    in
    Printf.sprintf "match { %s }" (arms |> List.map show_arm |> String.concat "|")
  | Num n -> Int64.to_string n
  | Rec (binder, body) ->
    Printf.sprintf "rec |%s| %s" (show_binder binder) (show_term body)
  | Arr terms ->
    let terms_str = terms |> List.map show_term |> String.concat ", " in
    Printf.sprintf "[%s]" terms_str
  | Ann (term, tyu) -> Printf.sprintf "(%s : %s)" (show_term term) (show_ty_use tyu)
  | Done -> "done"

and show_command cmd =
  match cmd with
  | Fork (cmd1, cmd2) ->
    Printf.sprintf "[%s | %s]" (show_command cmd1) (show_command cmd2)
  | Core { l_term; r_term } ->
    Printf.sprintf "%s . %s" (show_term l_term) (show_term r_term)
  | Arith arith_cmd -> show_arith_command arith_cmd

and show_arith_command arith_cmd =
  match arith_cmd with
  | Unop { op; in_term; out_term } ->
    Printf.sprintf "%s(%s | %s)" (show_unop op) (show_term in_term) (show_term out_term)
  | Bop { op; l_term; r_term; out_term } ->
    Printf.sprintf
      "%s(%s, %s | %s)"
      (show_bop op)
      (show_term l_term)
      (show_term r_term)
      (show_term out_term)
;;

let rec show_definition def =
  match def with
  | TermDef (binder, term) ->
    Printf.sprintf "let %s = %s" (show_binder binder) (show_term term)
  | TypeDef (kind_binder, ty) ->
    Printf.sprintf "type %s = %s" (show_kind_binder kind_binder) (show_ty ty)
  | ModuleDef { name; program } ->
    Printf.sprintf "module %s {\n%s\n}" name (show_program program)

and show_open mo =
  match mo with
  | Open name -> Printf.sprintf "open %s" (show_name name)
  | Use { mod_name; use_name } ->
    Printf.sprintf "use %s as %s" (show_name mod_name) use_name

and show_program prog =
  let opens_str = prog.opens |> List.map show_open |> String.concat "\n" in
  let defs_str = prog.definitions |> List.map show_definition |> String.concat "\n" in
  let command_str = Option.fold ~none:"" ~some:show_command prog.command in
  Printf.sprintf "%s\n%s\n%s" opens_str defs_str command_str
;;
