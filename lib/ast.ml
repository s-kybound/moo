type unop =
  | Neg
  | Not

type bop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | Xor
  | Shl
  | Shr

type name =
  | Base of string
  | Namespaced of
      { namespace : string
      ; inner : name
      }

type polarity =
  | Plus
  | Minus

type mode =
  | By_value
  | By_name

type shape =
  | Data
  | Codata

type ty_use =
  | Polarised of polarity * moded_ty
  | Abstract of
      { negated : bool
      ; name : string
      }

and moded_ty = mode option * ty

and ty =
  | Named of name * ty_use list
  | Raw of shape * raw_ty

and raw_ty =
  | Raw64
  | Unit
  | Product of ty_use list
  | Array of ty_use
  | ADT of variant list

and variant = string * ty_use list

type kind_binder = string * string list

type binder =
  { name : string
  ; typ : ty_use option
  }

type pattern =
  | Var of binder
  | Wildcard
  | Tup of pattern list
  | Constr of
      { pat_name : name
      ; pat_args : pattern list
      }

type term =
  | Mu of binder * command (* mu and mu tilde *)
  | Variable of name
  | Construction of
      { cons_name : name
      ; cons_args : term list
      }
  | Tuple of term list
  | Matcher of (pattern * command) list (* match and dispatch *)
  | Num of int64
  | Rec of binder * term (* fixpoint term *)
  | Arr of term list
  | Done

and command =
  | Core of
      { l_term : term
      ; r_term : term
      }
  | Arith of arith_command
  | Fork of command * command

and arith_command =
  | Unop of
      { op : unop
      ; in_term : term
      ; out_term : term
      }
  | Bop of
      { op : bop
      ; l_term : term
      ; r_term : term
      ; out_term : term
      }

type definition =
  | TermDef of binder * term
  | TypeDef of kind_binder * ty

type t = { definitions : definition list }

(* prints the program exactly as is *)
module Show_program = struct
  let rec show_name name =
    match name with
    | Namespaced { namespace; inner } ->
      Printf.sprintf "%s::%s" namespace (show_name inner)
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

  and show_moded_ty (mode_opt, ty) =
    match mode_opt with
    | Some m -> Printf.sprintf "[%s]%s" (show_mode m) (show_ty ty)
    | None -> Printf.sprintf "[???]%s" (show_ty ty)

  and show_ty ty =
    match ty with
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

  and show_variant (name, params) =
    let params_str = params |> List.map show_ty_use |> String.concat ", " in
    Printf.sprintf "%s(%s)" name params_str
  ;;

  let show_kind_binder (name, params) =
    let params_str = String.concat ", " params in
    Printf.sprintf "%s<%s>" name params_str
  ;;

  let show_binder binder =
    match binder.typ with
    | Some tyu -> Printf.sprintf "%s:%s" binder.name (show_ty_use tyu)
    | None -> binder.name
  ;;

  let rec show_pattern pat =
    match pat with
    | Wildcard -> "_"
    | Var binder -> show_binder binder
    | Constr { pat_name; pat_args } ->
      let args_str = pat_args |> List.map show_pattern |> String.concat ", " in
      Printf.sprintf "%s(%s)" (show_name pat_name) args_str
    | Tup pats ->
      let pats_str = pats |> List.map show_pattern |> String.concat ", " in
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

  let show_definition def =
    match def with
    | TermDef (binder, term) ->
      Printf.sprintf "let %s = %s" (show_binder binder) (show_term term)
    | TypeDef (kind_binder, ty) ->
      Printf.sprintf "type %s = %s" (show_kind_binder kind_binder) (show_ty ty)
  ;;

  let show_program prog =
    prog.definitions |> List.map show_definition |> String.concat ";\n"
  ;;
end
