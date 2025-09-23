(* This is the user facing AST of moo. 
 * The variables should be converted into using de Brujin indices
 * by a first pass before further execution. *)
module Surface = struct
  type name = string

  type producer =
    | Mu of name * cut
    | Pair of neutral * neutral
    | Cosplit of name * name * cut

  and consumer =
    | MuTilde of name * cut
    | Split of name * name * cut
    | Copair of neutral * neutral

  and cut =
    { p : neutral
    ; c : neutral
    }

  and neutral =
    | Name of name
    | Positive of producer
    | Negative of consumer

  type definition =
    | Producer of name * producer
    | Consumer of name * consumer

  type t =
    { definitions : definition list
    ; main : cut
    }

  (* Surface's show should look exactly like the code.
   * but Core will look closer to product-mu-mu calculus.
  *)
  module Show = struct
    let rec show_producer p =
      match p with
      | Mu (coname, cut) -> Printf.sprintf "(letcc %s %s)" coname (show_cut cut)
      | Pair (a, b) -> Printf.sprintf "(pair %s %s)" (show_neutral a) (show_neutral b)
      | Cosplit (a, b, cut) -> Printf.sprintf "(cosplit %s %s %s)" a b (show_cut cut)

    and show_consumer c =
      match c with
      | MuTilde (name, cut) -> Printf.sprintf "(let %s %s)" name (show_cut cut)
      | Split (a, b, cut) -> Printf.sprintf "(split %s %s %s)" a b (show_cut cut)
      | Copair (a, b) -> Printf.sprintf "(copair %s %s)" (show_neutral a) (show_neutral b)

    and show_cut (cut : cut) =
      Printf.sprintf "[%s %s]" (show_neutral cut.p) (show_neutral cut.c)

    and show_neutral n =
      match n with
      | Name n -> n
      | Positive p -> show_producer p
      | Negative c -> show_consumer c
    ;;

    let show t = show_cut t.main
  end

  module Producer = struct
    let mu coname cut = Mu (coname, cut)
    let pair a b = Pair (a, b)
    let cosplit a b cut = Cosplit (a, b, cut)
  end

  module Consumer = struct
    let mutilde name cut = MuTilde (name, cut)
    let split a b cut = Split (a, b, cut)
    let copair a b = Copair (a, b)
  end

  module Neutral = struct
    let identifier name = Name name
  end

  let defp (name : name) (input : name) (body : cut) = Producer (name, Mu (input, body))

  let defc (name : name) (input : name) (body : cut) =
    Consumer (name, MuTilde (input, body))
  ;;

  let cut p c = { p; c }
  let program definitions main = { definitions; main }
end

(* Core AST uses de Bruijn indices for bound variables/covariables.
 * 
 * Both names and conames are converted to de Bruijn indices, sharing
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

  and consumer =
    | MuTilde of cut
    | Split of cut
    | Copair of neutral * neutral

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

  type t =
    { definitions : definition list
    ; main : cut
    }

  module Show = struct
    let show_identifer name =
      match name with
      | Free name -> name
      | Bound n -> string_of_int n
    ;;

    let rec show_producer p =
      match p with
      | Mu cut -> Printf.sprintf "(μ.%s)" (show_cut cut)
      | Pair (a, b) -> Printf.sprintf "(%s * %s)" (show_neutral a) (show_neutral b)
      | Cosplit cut -> Printf.sprintf "((0 & 1).%s)" (show_cut cut)

    and show_consumer c =
      match c with
      | MuTilde cut -> Printf.sprintf "(μ̃.%s)" (show_cut cut)
      | Split cut -> Printf.sprintf "((0 * 1).%s)" (show_cut cut)
      | Copair (a, b) -> Printf.sprintf "(%s & %s)" (show_neutral a) (show_neutral b)

    and show_cut (cut : cut) =
      Printf.sprintf "<%s|%s>" (show_neutral cut.p) (show_neutral cut.c)

    and show_neutral n =
      match n with
      | Name n -> show_identifer n
      | Positive p -> show_producer p
      | Negative c -> show_consumer c
    ;;

    let show t = show_cut t.main
  end

  module Converter = struct
    module S = Surface

    (* our environment tracks a single combined stack of names and conames *)
    type env = S.name list

    let name_match n m = String.equal n m
    let empty_env = []

    let lookup_identifier env n =
      let rec aux stack n depth =
        match stack with
        | [] -> Free n
        | n' :: stack' -> if name_match n n' then Bound depth else aux stack' n (depth + 1)
      in
      aux env n 0
    ;;

    let push_name v env = v :: env

    let rec convert_producer env p : producer =
      match p with
      | S.Mu (k, cut) -> Mu (convert_cut (push_name k env) cut)
      | S.Pair (a, b) -> Pair (convert_neutral env a, convert_neutral env b)
      | S.Cosplit (x, y, cut) ->
        if name_match x y
        then raise (Failure "Cosplit: name conflict in parameters")
        else (
          (* it is x first, then y, so that
           * x will be the first to be looked up (0)
           * then y (1) *)
          let env' = x :: y :: env in
          Cosplit (convert_cut env' cut))

    and convert_consumer env c : consumer =
      match c with
      | S.MuTilde (v, cut) -> MuTilde (convert_cut (push_name v env) cut)
      | S.Split (x, y, cut) ->
        if name_match x y
        then raise (Failure "Split: name conflict in parameters")
        else (
          let env' = x :: y :: env in
          Split (convert_cut env' cut))
      | S.Copair (a, b) -> Copair (convert_neutral env a, convert_neutral env b)

    and convert_cut env cut : cut =
      { p = convert_neutral env cut.p; c = convert_neutral env cut.c }

    and convert_neutral env neutral : neutral =
      match neutral with
      | S.Name n -> Name (lookup_identifier env n)
      | S.Positive p -> Positive (convert_producer env p)
      | S.Negative c -> Negative (convert_consumer env c)
    ;;

    (* definitions are evaluated without environment *)
    let convert_definition definition : definition =
      match definition with
      | S.Producer (n, p) -> Producer (n, convert_producer empty_env p)
      | S.Consumer (cn, c) -> Consumer (cn, convert_consumer empty_env c)
    ;;
  end

  let convert (t : Surface.t) : t =
    { definitions = List.map Converter.convert_definition t.definitions
    ; main = Converter.convert_cut Converter.empty_env t.main
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
