open Ast

let show_name (name : name) =
  match name with
  | Namespaced (namespaces, inner) ->
    Printf.sprintf "%s::%s" (String.concat "::" namespaces) inner
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

let show_unify_ty { name; left_focusing } =
  let focus_str = if left_focusing then "<-" else "->" in
  Printf.sprintf "%s%s" name focus_str
;;

let rec show_ty_use tyu =
  match tyu with
  | Polarised (pol, t) -> Printf.sprintf "%s%s" (show_polarity pol) (show_ty t)
  | Abstract { negated; name } -> if negated then Printf.sprintf "~%s" name else name
  | AbstractIntroducer (ty, ty_use) ->
    Printf.sprintf "[%s]%s" (show_unify_ty ty) (show_ty_use ty_use)
  | Weak { link = { negated; meta } } ->
  match describe_meta_var meta with
  | `Unknown id ->
    let prefix = if negated then "~" else "" in
    Printf.sprintf "%s?%d" prefix id
  | `Shaped (id, cons) ->
    let shape = if cons <> negated then "constructor" else "destructor" in
    Printf.sprintf "[inferred-?%d]%s" id shape
  | `Inferred (id, constructor, raw) ->
    let is_constructor = constructor <> negated in
    Printf.sprintf
      "[inferred-?%d]%sdata %s"
      id
      (if is_constructor then "+" else "-")
      (show_raw_ty raw)
  | `Unified tyu ->
    if negated then Printf.sprintf "~(%s)" (show_ty_use tyu) else show_ty_use tyu

and describe_meta_var { id; cell } =
  match cell with
  | Unified tyu -> `Unified tyu
  | Inferred { constructor; raw_lower_bound } ->
  match constructor, raw_lower_bound with
  | Some cons, Some raw -> `Inferred (id, cons, raw)
  | Some cons, None -> `Shaped (id, cons)
  | _, _ -> `Unknown id

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

let show_binder ?(ann_show = fun _ s -> s) binder =
  match binder with
  | Wildcard ann -> ann_show ann "_"
  | Var (ann, name) -> ann_show ann name
;;

let show_pattern ~ann_show pat =
  match pat with
  | Binder pb -> show_binder ~ann_show pb
  | Constr { pat_name; pat_args } ->
    let args_str = pat_args |> List.map (show_binder ~ann_show) |> String.concat ", " in
    Printf.sprintf "%s(%s)" (show_name pat_name) args_str
  | Tup pats ->
    let pats_str = pats |> List.map (show_binder ~ann_show) |> String.concat ", " in
    Printf.sprintf "(%s)" pats_str
  | Numeral n -> Int64.to_string n
;;

let rec show_term ~ann_show (ann, term) =
  let term_str =
    match term with
    | Mu (binder, cmd) ->
      Printf.sprintf
        "{ %s -> %s }"
        (show_binder ~ann_show binder)
        (show_command ~ann_show cmd)
    | Variable name -> show_name name
    | Construction { cons_name; cons_args } ->
      let args_str = cons_args |> List.map (show_term ~ann_show) |> String.concat ", " in
      Printf.sprintf "%s(%s)" (show_name cons_name) args_str
    | Tuple terms ->
      let terms_str = terms |> List.map (show_term ~ann_show) |> String.concat ", " in
      Printf.sprintf "(%s)" terms_str
    | Matcher arms ->
      let show_arm (pat, cmd) =
        Printf.sprintf
          "%s -> %s"
          (show_pattern ~ann_show pat)
          (show_command ~ann_show cmd)
      in
      Printf.sprintf "match { %s }" (arms |> List.map show_arm |> String.concat "|")
    | Num n -> Int64.to_string n
    | Rec (binder, body) ->
      Printf.sprintf
        "rec |%s| %s"
        (show_binder ~ann_show binder)
        (show_term ~ann_show body)
    | Arr terms ->
      let terms_str = terms |> List.map (show_term ~ann_show) |> String.concat ", " in
      Printf.sprintf "[%s]" terms_str
    | Ann (term, tyu) ->
      Printf.sprintf "(%s : %s)" (show_term ~ann_show term) (show_ty_use tyu)
    | Exit -> "exit"
  in
  ann_show ann term_str

and show_command ~ann_show (ann, cmd) =
  let cmd_str =
    match cmd with
    | Fork (cmd1, cmd2) ->
      Printf.sprintf
        "[%s | %s]"
        (show_command ~ann_show cmd1)
        (show_command ~ann_show cmd2)
    | Core { l_term; r_term } ->
      Printf.sprintf "%s . %s" (show_term ~ann_show l_term) (show_term ~ann_show r_term)
    | Arith arith_cmd -> show_arith_command ~ann_show arith_cmd
  in
  ann_show ann cmd_str

and show_arith_command ~ann_show arith_cmd =
  match arith_cmd with
  | Unop { op; in_term; out_term } ->
    Printf.sprintf
      "%s(%s | %s)"
      (show_unop op)
      (show_term ~ann_show in_term)
      (show_term ~ann_show out_term)
  | Bop { op; l_term; r_term; out_term } ->
    Printf.sprintf
      "%s(%s, %s | %s)"
      (show_bop op)
      (show_term ~ann_show l_term)
      (show_term ~ann_show r_term)
      (show_term ~ann_show out_term)
;;

let rec show_mod_tli ~ann_show def =
  match def with
  | TermDef (binder, term) ->
    Printf.sprintf "let %s = %s" (show_binder ~ann_show binder) (show_term ~ann_show term)
  | TypeDef (name, abstracts, ty) ->
    Printf.sprintf "type %s%s = %s" name (show_abstracts abstracts) (show_ty ty)
  | Term term -> show_term ~ann_show term

and show_abstracts abstracts =
  match abstracts with
  | [] -> ""
  | _ ->
    let abstracts_str = String.concat ", " abstracts in
    Printf.sprintf "<%s>" abstracts_str

and show_open (mo : Surface.module_open) =
  match mo with
  (* | Open name -> Printf.sprintf "open %s" (show_name name) *)
  | Use { mod_name; use_name } ->
    Printf.sprintf "use %s as %s" (show_name mod_name) use_name

and show_program ~ann_show prog =
  prog |> List.map (show_top_level_item ~ann_show show_mod_tli) |> String.concat "\n"

and show_top_level_item ~ann_show show_mod_tli (tli : 'a Surface.top_level_item) =
  match tli with
  | Open o -> show_open o
  | Def d -> show_mod_tli ~ann_show d
;;
