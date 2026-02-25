open Ast

let rec show_name (name : name) =
  match name with
  | Namespaced { namespace; inner } -> Printf.sprintf "%s::%s" namespace (show_name inner)
  | Base s -> s
;;

let show_unop (op : unop) =
  match op with
  | Not -> "!"
  | Neg -> "-"
;;

let show_bop (op : bop) =
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

let show_polarity (p : polarity) =
  match p with
  | Plus -> "+"
  | Minus -> "-"
;;

let show_mode (m : mode) =
  match m with
  | By_value -> "cbv"
  | By_name -> "cbn"
;;

let show_shape (s : shape) =
  match s with
  | Data -> "data"
  | Codata -> "codata"
;;

let rec show_ty_use tyu =
  match tyu with
  | Polarised (pol, t) -> Printf.sprintf "%s%s" (show_polarity pol) (show_ty t)
  | Abstract { negated; name } -> if negated then Printf.sprintf "~%s" name else name
  | AbstractIntroducer (name, ty_use) -> Printf.sprintf "[%s]%s" name (show_ty_use ty_use)
  | Weak { negated; meta } ->
    if negated then Printf.sprintf "~%s" (show_meta_var meta) else show_meta_var meta

and show_meta_var { id; cell } =
  match cell with
  | Inferred { constructor; raw_lower_bound } ->
    (* only case that matters is when we have enough information to 
     * say what type it's meant to be *)
    begin match constructor, raw_lower_bound with
    | Some cons, Some raw ->
      if cons then show_raw_ty raw else Printf.sprintf "destructor(%s)" (show_raw_ty raw)
    | _, _ -> Printf.sprintf "?%d" id
    end
  | Unified tyu -> Printf.sprintf "%s" (show_ty_use tyu)

and show_ty ty =
  match ty with
  | Named (name, []) -> show_name name
  | Named (name, params) ->
    let params_str = params |> List.map show_ty_use |> String.concat ", " in
    Printf.sprintf "%s<%s>" (show_name name) params_str
  | Raw (mode, shape, raw) ->
    Printf.sprintf "%s[%s] %s" (show_shape shape) (show_mode mode) (show_raw_ty raw)

and show_raw_ty raw =
  match raw with
  | Raw64 -> "raw64"
  | Product [] -> "unit"
  | Product tys ->
    let tys_str = tys |> List.map show_ty_use |> String.concat ", " in
    Printf.sprintf "(%s)" tys_str
  | Array tyu -> Printf.sprintf "[%s]" (show_ty_use tyu)
  | Variant variants ->
    let variants_str = variants |> List.map show_variant |> String.concat " | " in
    Printf.sprintf "variant { %s }" variants_str

and show_variant { constr_name; constr_args } =
  match constr_args with
  | [] -> constr_name
  | _ ->
    let params_str = constr_args |> List.map show_ty_use |> String.concat ", " in
    Printf.sprintf "%s(%s)" constr_name params_str
;;

let show_kind_binder (name, params) =
  match params with
  | [] -> name
  | _ ->
    let params_str = String.concat ", " params in
    Printf.sprintf "%s<%s>" name params_str
;;

let show_binder binder =
  match binder with
  | Wildcard _ -> "_"
  | Var (_, name) -> name
;;

let show_pattern pat =
  match pat with
  | Binder pb -> show_binder pb
  | Constr { pat_name; pat_args } ->
    let args_str = pat_args |> List.map show_binder |> String.concat ", " in
    Printf.sprintf "%s(%s)" (show_name pat_name) args_str
  | Tup pats ->
    let pats_str = pats |> List.map show_binder |> String.concat ", " in
    Printf.sprintf "(%s)" pats_str
  | Numeral n -> Int64.to_string n
;;

let rec show_term (_, term) =
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
  | Exit -> "exit"

and show_command (_, cmd) =
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

and show_open (mo : Surface.module_open) =
  match mo with
  | Open name -> Printf.sprintf "open %s" (show_name name)
  | Use { mod_name; use_name } ->
    Printf.sprintf "use %s as %s" (show_name mod_name) use_name

and show_program (prog, cmd) =
  (prog |> List.map (show_top_level_item show_definition))
  @ Option.to_list (Option.map show_command cmd)
  |> String.concat "\n"

and show_top_level_item (show_definition : 'a -> string) (tli : 'a Surface.top_level_item)
  =
  match tli with
  | Open o -> show_open o
  | Def d -> show_definition d
;;
