module Type = struct
  type type_schema =
    | Base of string
    | Kind of string * string list

  type abstract_type =
    | Var of string
    | Neg of abstract_type

  type type_expr =
    | Name of string
    | PosProd of type_use * type_use
    | NegProd of type_use * type_use
    | KindInstantiation of string * type_use list

  and type_use =
    | Abstract of abstract_type
    | Instantiated of polar_type

  and polar_type =
    | Pos of type_expr
    | Neg of type_expr

  module Show = struct
    let show_type_schema ts =
      match ts with
      | Base s -> s
      | Kind (k, params) -> Printf.sprintf "(%s %s)" k (String.concat " " params)
    ;;

    let rec show_abstract_type at =
      match at with
      | Var s -> s
      | Neg at' -> Printf.sprintf "~%s" (show_abstract_type at')
    ;;

    let rec show_type_expr te =
      match te with
      | Name s -> s
      | PosProd (tu1, tu2) ->
        Printf.sprintf "(* %s %s)" (show_type_use tu1) (show_type_use tu2)
      | NegProd (tu1, tu2) ->
        Printf.sprintf "(& %s %s)" (show_type_use tu1) (show_type_use tu2)
      | KindInstantiation (k, args) ->
        Printf.sprintf "(%s %s)" k (String.concat " " (List.map show_type_use args))

    and show_type_use tu =
      match tu with
      | Abstract at -> show_abstract_type at
      | Instantiated pt -> show_polar_type pt

    and show_polar_type pt =
      match pt with
      | Pos te -> Printf.sprintf "%s+" (show_type_expr te)
      | Neg te -> Printf.sprintf "%s-" (show_type_expr te)
    ;;
  end
end

(* This is the user facing AST of moo. 
 * The variables should be converted into using de Brujin indices
 * by a first pass before further execution. *)
module Surface = struct
  type name =
    { name : string
    ; typ : Type.polar_type option
    }

  type producer =
    | Mu of name * cut
    | Pair of neutral * neutral
    | Cosplit of name * name * cut
    | Unit
    | Codo of cut

  and consumer =
    | MuTilde of name * cut
    | Split of name * name * cut
    | Copair of neutral * neutral
    | Counit
    | Do of cut

  and cut =
    { p : neutral
    ; c : neutral
    }

  and neutral =
    | Name of string
    | Positive of producer
    | Negative of consumer

  type definition =
    | Producer of name * producer
    | Consumer of name * consumer
    | TypeDef of Type.type_schema * Type.type_expr

  type t =
    { definitions : definition list
    ; main : cut
    }

  (* Surface's show should look exactly like the code.
   * but Core will look closer to product-mu-mu calculus.
  *)
  module Show = struct
    let show_name n =
      match n.typ with
      | None -> n.name
      | Some typ -> Printf.sprintf "[%s : %s]" n.name (Type.Show.show_polar_type typ)
    ;;

    let rec show_producer p =
      match p with
      | Mu (coname, cut) ->
        Printf.sprintf "(letcc %s %s)" (show_name coname) (show_cut cut)
      | Pair (a, b) -> Printf.sprintf "(pair %s %s)" (show_neutral a) (show_neutral b)
      | Cosplit (a, b, cut) ->
        Printf.sprintf "(cosplit %s %s %s)" (show_name a) (show_name b) (show_cut cut)
      | Unit -> "()"
      | Codo cut -> Printf.sprintf "(codo %s)" (show_cut cut)

    and show_consumer c =
      match c with
      | MuTilde (name, cut) ->
        Printf.sprintf "(let %s %s)" (show_name name) (show_cut cut)
      | Split (a, b, cut) ->
        Printf.sprintf "(split %s %s %s)" (show_name a) (show_name b) (show_cut cut)
      | Copair (a, b) -> Printf.sprintf "(copair %s %s)" (show_neutral a) (show_neutral b)
      | Counit -> "'()"
      | Do cut -> Printf.sprintf "(do %s)" (show_cut cut)

    and show_cut (cut : cut) =
      Printf.sprintf "[%s %s]" (show_neutral cut.p) (show_neutral cut.c)

    and show_neutral n =
      match n with
      | Name n -> n
      | Positive p -> show_producer p
      | Negative c -> show_consumer c
    ;;

    let show_definition def =
      match def with
      | Producer (name, body) ->
        Printf.sprintf "defp %s = %s;;" (show_name name) (show_producer body)
      | Consumer (name, body) ->
        Printf.sprintf "defc %s = %s;;" (show_name name) (show_consumer body)
      | TypeDef (schema, expr) ->
        Printf.sprintf
          "type %s = %s;;"
          (Type.Show.show_type_schema schema)
          (Type.Show.show_type_expr expr)
    ;;

    let show t =
      let defs_str = String.concat "\n" (List.map show_definition t.definitions) in
      let main_str = show_cut t.main in
      if defs_str = "" then main_str else Printf.sprintf "%s\n\n%s" defs_str main_str
    ;;
  end

  module Producer = struct
    let mu coname cut = Mu (coname, cut)
    let pair a b = Pair (a, b)
    let cosplit a b cut = Cosplit (a, b, cut)
    let unit = Unit
    let codo cut = Codo cut
  end

  module Consumer = struct
    let mutilde name cut = MuTilde (name, cut)
    let split a b cut = Split (a, b, cut)
    let copair a b = Copair (a, b)
    let counit = Counit
    let do_ cut = Do cut
  end

  module Neutral = struct
    let identifier name = Name name
  end

  let make_name (ident : string) (typ : Type.polar_type option) = { name = ident; typ }
  let defp (name : name) (input : name) (body : cut) = Producer (name, Mu (input, body))

  let defc (name : name) (input : name) (body : cut) =
    Consumer (name, MuTilde (input, body))
  ;;

  let cut p c = { p; c }
  let program definitions main = { definitions; main }
end

(* Core AST uses de Brujin indices for bound variables/covariables.
 * 
 * Both names and conames are converted to de Brujin indices, sharing
 * a single binding environment. Each binder (μ, μ̃, cosplit, split) 
 * introduces variables at indices 0, 1, etc., with outer bindings
 * shifted accordingly.
 * 
 * eg. (letcc x ... x ... (let p ... x p ...)) -> (letcc ... 0 ... (let ... 1 0 ...)) *)
module Core = struct
  type identifier =
    | Free of string
    | Bound of int

  type producer =
    | Mu of cut
    | Pair of neutral * neutral
    | Cosplit of cut
    | Unit
    | Codo of cut

  and consumer =
    | MuTilde of cut
    | Split of cut
    | Copair of neutral * neutral
    | Counit
    | Do of cut

  and cut =
    { p : neutral
    ; c : neutral
    }

  and neutral =
    | Name of identifier
    | Positive of producer
    | Negative of consumer

  type definition =
    | Producer of string * producer
    | Consumer of string * consumer
    | TypeDef of Type.type_schema * Type.type_expr

  type t =
    { definitions : definition list
    ; main : cut
    }

  module Show = struct
    let show_identifier name =
      match name with
      | Free name -> name
      | Bound n -> string_of_int n
    ;;

    let rec show_producer p =
      match p with
      | Mu cut -> Printf.sprintf "(μ.%s)" (show_cut cut)
      | Pair (a, b) -> Printf.sprintf "(%s * %s)" (show_neutral a) (show_neutral b)
      | Cosplit cut -> Printf.sprintf "((0 & 1).%s)" (show_cut cut)
      | Unit -> "()"
      | Codo cut -> Printf.sprintf "(codo %s)" (show_cut cut)

    and show_consumer c =
      match c with
      | MuTilde cut -> Printf.sprintf "(μ̃.%s)" (show_cut cut)
      | Split cut -> Printf.sprintf "((0 * 1).%s)" (show_cut cut)
      | Copair (a, b) -> Printf.sprintf "(%s & %s)" (show_neutral a) (show_neutral b)
      | Counit -> "'()"
      | Do cut -> Printf.sprintf "(do %s)" (show_cut cut)

    and show_cut (cut : cut) =
      Printf.sprintf "<%s|%s>" (show_neutral cut.p) (show_neutral cut.c)

    and show_neutral n =
      match n with
      | Name n -> show_identifier n
      | Positive p -> show_producer p
      | Negative c -> show_consumer c
    ;;

    let show_definition def =
      match def with
      | Producer (name, body) -> Printf.sprintf "defp %s = %s;;" name (show_producer body)
      | Consumer (name, body) -> Printf.sprintf "defc %s = %s;;" name (show_consumer body)
      | TypeDef (schema, expr) ->
        Printf.sprintf
          "type %s = %s;;"
          (Type.Show.show_type_schema schema)
          (Type.Show.show_type_expr expr)
    ;;

    let show t =
      let defs_str = String.concat "\n" (List.map show_definition t.definitions) in
      let main_str = show_cut t.main in
      if defs_str = "" then main_str else Printf.sprintf "%s\n\n%s" defs_str main_str
    ;;
  end

  module Converter = struct
    module S = Surface

    type term_env = string list

    let name_match = String.equal
    let empty_term_env : term_env = []

    let lookup_identifier env n =
      let rec aux stack n depth =
        match stack with
        | [] -> Free n
        | n' :: stack' -> if name_match n n' then Bound depth else aux stack' n (depth + 1)
      in
      aux env n 0
    ;;

    let push_name (v : S.name) env = v.name :: env

    let rec convert_producer term_env p : producer =
      match p with
      | S.Mu (k, cut) -> Mu (convert_cut (push_name k term_env) cut)
      | S.Pair (a, b) -> Pair (convert_neutral term_env a, convert_neutral term_env b)
      | S.Cosplit (x, y, cut) ->
        let x, y = x.name, y.name in
        if name_match x y
        then raise (Failure "Cosplit: name conflict in parameters")
        else (
          (* it is x first, then y, so that
           * x will be the first to be looked up (0)
           * then y (1) *)
          let term_env' = x :: y :: term_env in
          Cosplit (convert_cut term_env' cut))
      | S.Unit -> Unit
      | S.Codo cut -> Codo (convert_cut term_env cut)

    and convert_consumer term_env c : consumer =
      match c with
      | S.MuTilde (v, cut) -> MuTilde (convert_cut (push_name v term_env) cut)
      | S.Split (x, y, cut) ->
        let x, y = x.name, y.name in
        if name_match x y
        then raise (Failure "Split: name conflict in parameters")
        else (
          let term_env' = x :: y :: term_env in
          Split (convert_cut term_env' cut))
      | S.Copair (a, b) -> Copair (convert_neutral term_env a, convert_neutral term_env b)
      | S.Counit -> Counit
      | S.Do cut -> Do (convert_cut term_env cut)

    and convert_cut term_env cut : cut =
      { p = convert_neutral term_env cut.p; c = convert_neutral term_env cut.c }

    and convert_neutral term_env neutral : neutral =
      match neutral with
      | S.Name n -> Name (lookup_identifier term_env n)
      | S.Positive p -> Positive (convert_producer term_env p)
      | S.Negative c -> Negative (convert_consumer term_env c)
    ;;

    (* definitions are evaluated without environment *)
    let convert_definition definition : definition =
      match definition with
      | S.Producer (n, p) -> Producer (n.name, convert_producer empty_term_env p)
      | S.Consumer (cn, c) -> Consumer (cn.name, convert_consumer empty_term_env c)
      | S.TypeDef (schema, expr) -> TypeDef (schema, expr)
    ;;
  end

  let convert (t : Surface.t) : t =
    { definitions = List.map Converter.convert_definition t.definitions
    ; main = Converter.convert_cut Converter.empty_term_env t.main
    }
  ;;

  let rec aequiv_producer (a : producer) (b : producer) =
    match a, b with
    | Mu cut, Mu cut' -> aequiv_cut cut cut'
    | Pair (a, b), Pair (c, d) -> aequiv_neutral a c && aequiv_neutral b d
    | Cosplit cut, Cosplit cut' -> aequiv_cut cut cut'
    | _, _ -> false

  and aequiv_consumer (a : consumer) (b : consumer) =
    match a, b with
    | MuTilde cut, MuTilde cut' -> aequiv_cut cut cut'
    | Split cut, Split cut' -> aequiv_cut cut cut'
    | Copair (a, b), Copair (c, d) -> aequiv_neutral a c && aequiv_neutral b d
    | _, _ -> false

  and aequiv_cut (a : cut) (b : cut) = aequiv_neutral a.p b.p && aequiv_neutral a.c b.c

  and aequiv_neutral (a : neutral) (b : neutral) =
    match a, b with
    | Positive a, Positive b -> aequiv_producer a b
    | Negative a, Negative b -> aequiv_consumer a b
    | _, _ -> false
  ;;
end
