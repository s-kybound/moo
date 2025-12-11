type unop =
  | Neg
  | Not

type bop =
  | Add
  | Sub
  | Mul
  | Sdiv
  | Mod
  | And
  | Or
  | Xor
  | Shl
  | Lshr
  | Ashr

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
  | CBV
  | CBN

type shape =
  | Data
  | Codata

type ty =
  | Named of mode * kind_inst
  | Raw of mode * core_ty

and kind_inst = name * ty_use list
and core_ty = shape * raw_ty

and raw_ty =
  | Raw64
  | Unit
  | Product of ty_use list
  | ADT of variant list

and variant = name * ty_use list

and ty_use =
  | Polarised of polarity * ty
  | Abstract of
      { negated : bool
      ; name : string
      }

type kind_binder = name * string list

type binder =
  { name : name
  ; typ : ty_use option
  }

type pattern =
  | Wildcard
  | Var of binder
  | Constr of
      { pat_name : name
      ; pat_args : pattern list
      }

type term =
  | Binder of binder * command (* mu and mu tilde *)
  | Variable of name
  | Construction of construction
  | Matcher of (pattern * command) list (* match and dispatch *)
  | Num of int64
  | Done

and construction =
  { cons_name : name
  ; cons_args : term list
  }

and command =
  | Base of
      { l_term : term
      ; r_term : term
      }
  | Arith of arith_command

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

(* to handle definitions with introduced types *)
type definition_binder = binder * string list

type definition =
  | TermDef of
      { recursive : bool
      ; binder : definition_binder
      ; term : term
      }
  | TypeDef of kind_binder * ty

type t = { definitions : definition list }

(* prints the program exactly as is *)
module Show_program = struct

    let rec show_name name =
        match name with
        | Namespaced { namespace; inner } ->
            Printf.sprintf "%s::%s" namespace (show_name inner)
        | Base s -> s

    let show_unop op =
        match op with
        | Not -> "!"
        | Neg -> "-"

    let show_bop op =
        match op with
        | Add -> "+"
        | Sub -> "-"
        | Mul -> "*"
        | Sdiv -> "/"
        | Mod -> "%"
        | And -> "&"
        | Or -> "|"
        | Xor -> "^"
        | Shl -> "<<"
        | Lshr -> ">>"
        | Ashr -> ">>>"

    let show_polarity p =
        match p with
        | Plus -> "+"
        | Minus -> "-"

    let show_mode m =
        match m with
        | CBV -> "cbv"
        | CBN -> "cbn"

    let show_shape s =
        match s with
        | Data -> "data"
        | Codata -> "codata"

    let rec show_ty ty =
      match ty with
      | Named (mode, inst) -> 
        Printf.sprintf "[%s]%s" (show_mode mode) (show_kind_inst inst)
      | Raw (mode, core) -> 
        Printf.sprintf "[%s]%s" (show_mode mode) (show_core_ty core)
      
    and show_kind_inst (name, args) =
      let args_str = 
        args 
        |> List.map show_ty_use
        |> String.concat ", "
      in
      Printf.sprintf "%s<%s>" (show_name name) args_str

    and show_core_ty (shape, raw) =
      let raw_str =
        match raw with
        | Raw64 -> "raw64"
        | Unit -> "unit"
        | Product args ->
          let args_str = 
            args 
            |> List.map show_ty_use
            |> String.concat ", "
          in
          Printf.sprintf "(%s)" args_str
        | ADT variants ->
          let variant_to_str (vname, args) =
            let args_str = 
              args 
              |> List.map show_ty_use
              |> String.concat ", "
            in
            Printf.sprintf "%s(%s)" (show_name vname) args_str
          in
          let variants_str = 
            variants 
            |> List.map variant_to_str
            |> String.concat " | "
          in
          Printf.sprintf "{ %s }" variants_str
      in
      Printf.sprintf "%s %s" (show_shape shape) raw_str

    and show_ty_use tyu =
      match tyu with
      | Polarised (pol, ty) -> 
        Printf.sprintf "%s%s" (show_polarity pol) (show_ty ty)
      | Abstract { negated; name } -> 
        let neg_str = if negated then "~" else "" in
        Printf.sprintf "%s%s" neg_str name

    let show_kind_binder (name, params) =
      let params_str = String.concat ", " params in
      Printf.sprintf "%s<%s>" (show_name name) params_str

    let show_binder binder =
      match binder.typ with
      | Some tyu ->
        Printf.sprintf "%s: %s" (show_name binder.name) (show_ty_use tyu)
      | None ->
        show_name binder.name

    let rec show_pattern pat =
      match pat with
      | Wildcard -> "_"
      | Var binder -> show_binder binder
      | Constr { pat_name; pat_args } ->
        let args_str = 
          pat_args 
          |> List.map show_pattern
          |> String.concat ", "
        in
        Printf.sprintf "%s(%s)" (show_name pat_name) args_str

    let rec show_term term =
      match term with
      | Binder (binder, cmd) ->
        Printf.sprintf "{ %s -> %s }" (show_binder binder) (show_command cmd)
      | Variable name ->
        show_name name
      | Construction { cons_name; cons_args } ->
        let args_str = 
          cons_args 
          |> List.map show_term
          |> String.concat ", "
        in
        Printf.sprintf "%s(%s)" (show_name cons_name) args_str 
      | Matcher arms ->
        let show_arm (pat, cmd) =
          Printf.sprintf "%s -> %s" (show_pattern pat) (show_command cmd)
        in
        Printf.sprintf "match { %s }" 
          (arms 
          |> List.map show_arm 
          |> String.concat "|")
      | Num n ->
        Int64.to_string n
      | Done ->
        "done"
    and show_command cmd = 
      match cmd with
      | Base { l_term; r_term } ->
        Printf.sprintf "%s . %s" (show_term l_term) (show_term r_term)
      | Arith arith_cmd ->
        show_arith_command arith_cmd

    and show_arith_command arith_cmd =
      match arith_cmd with
      | Unop { op; in_term; out_term } ->
        Printf.sprintf "%s(%s, %s)" (show_unop op) (show_term in_term) (show_term out_term)
      | Bop { op; l_term; r_term ; out_term } ->
        Printf.sprintf "%s(%s, %s, %s)" (show_bop op) (show_term l_term) (show_term r_term) (show_term out_term)
      
    let show_definition def =
      match def with
      | TermDef { recursive; binder = (binder, type_params); term } ->
        let rec_str = if recursive then "rec " else "" in
        let type_params_str = 
          if type_params = [] then ""
          else 
            let params_str = String.concat ", " type_params in
            Printf.sprintf "<%s>" params_str
        in
        Printf.sprintf "%s%s%s = %s" rec_str (show_binder binder) type_params_str (show_term term)
      | TypeDef (kind_binder, ty) ->
        Printf.sprintf "type %s = %s" (show_kind_binder kind_binder) (show_ty ty)
    
end

