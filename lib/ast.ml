(* This is the user facing AST of moo. 
 * The variables should be converted into using de Brujin indices
 * by a first pass before further execution. *)
module Surface = struct
  type name = Name of string
  type coname = Coname of string

  type producer =
    | V of name
    | Mu of coname * cut
    | Pair of neutral * neutral
    | Cosplit of neutral_name * neutral_name * cut

  and consumer =
    | C of coname
    | MuTilde of name * cut
    | Split of neutral_name * neutral_name * cut
    | Copair of neutral * neutral

  and cut =
    { p : producer
    ; c : consumer
    }

  and neutral =
    | Positive of producer
    | Negative of consumer

  and neutral_name =
    | Positive_name of name
    | Negative_name of coname

  type t = cut

  (* Surface's show should look exactly like the code.
   * but Core will look closer to product-mu-mu calculus.
  *)
  module Show = struct
    let rec show_name (Name n) = n
    and show_coname (Coname c) = Printf.sprintf "'%s" c

    and show_producer p =
      match p with
      | V name -> show_name name
      | Mu (coname, cut) ->
        Printf.sprintf "(letcc %s %s)" (show_coname coname) (show_cut cut)
      | Pair (a, b) -> Printf.sprintf "(pair %s %s)" (show_neutral a) (show_neutral b)
      | Cosplit (a, b, cut) ->
        Printf.sprintf
          "(cosplit %s %s %s)"
          (show_neutral_name a)
          (show_neutral_name b)
          (show_cut cut)

    and show_consumer c =
      match c with
      | C coname -> show_coname coname
      | MuTilde (name, cut) ->
        Printf.sprintf "(let %s %s)" (show_name name) (show_cut cut)
      | Split (a, b, cut) ->
        Printf.sprintf
          "(split %s %s %s)"
          (show_neutral_name a)
          (show_neutral_name b)
          (show_cut cut)
      | Copair (a, b) -> Printf.sprintf "(copair %s %s)" (show_neutral a) (show_neutral b)

    and show_cut (cut : cut) =
      Printf.sprintf "[%s %s]" (show_producer cut.p) (show_consumer cut.c)

    and show_neutral n =
      match n with
      | Positive p -> show_producer p
      | Negative c -> show_consumer c

    and show_neutral_name n =
      match n with
      | Positive_name v -> show_name v
      | Negative_name c -> show_coname c
    ;;

    let show = show_cut
  end

  module Identifier = struct
    let name n = Name n
    let coname c = Coname c
  end

  module Producer = struct
    let variable name = V name
    let mu coname cut = Mu (coname, cut)
    let pair a b = Pair (a, b)
    let cosplit a b cut = Cosplit (a, b, cut)
  end

  module Consumer = struct
    let covariable coname = C coname
    let mutilde name cut = MuTilde (name, cut)
    let split a b cut = Split (a, b, cut)
    let copair a b = Copair (a, b)
  end

  let cut p c = { p; c }
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
    | FreeP of string
    | FreeC of string
    | Bound of int

  type producer =
    | V of identifier
    | Mu of cut
    | Pair of neutral * neutral
    | Cosplit of cut

  and consumer =
    | C of identifier
    | MuTilde of cut
    | Split of cut
    | Copair of neutral * neutral

  and cut =
    { p : producer
    ; c : consumer
    }

  and neutral =
    | Positive of producer
    | Negative of consumer

  type t = cut

  module Show = struct
    let show_identifer name =
      match name with
      | FreeP name -> name
      | FreeC name -> Printf.sprintf "'%s" name
      | Bound n -> string_of_int n
    ;;

    let rec show_producer p =
      match p with
      | V name -> show_identifer name
      | Mu cut -> Printf.sprintf "(μ.%s)" (show_cut cut)
      | Pair (a, b) -> Printf.sprintf "(%s * %s)" (show_neutral a) (show_neutral b)
      | Cosplit cut -> Printf.sprintf "((0 & 1).%s)" (show_cut cut)

    and show_consumer c =
      match c with
      | C coname -> show_identifer coname
      | MuTilde cut -> Printf.sprintf "(μ̃.%s)" (show_cut cut)
      | Split cut -> Printf.sprintf "((0 * 1).%s)" (show_cut cut)
      | Copair (a, b) -> Printf.sprintf "(%s & %s)" (show_neutral a) (show_neutral b)

    and show_cut (cut : cut) =
      Printf.sprintf "<%s|%s>" (show_producer cut.p) (show_consumer cut.c)

    and show_neutral n =
      match n with
      | Positive p -> show_producer p
      | Negative c -> show_consumer c
    ;;

    let show = show_cut
  end

  module Converter = struct
    module S = Surface

    (* our environment tracks a single combined stack of names and conames *)
    type env = S.neutral_name list

    let neutral_name_match n m =
      match n, m with
      | S.Positive_name (S.Name n), S.Positive_name (S.Name m) -> String.equal n m
      | S.Negative_name (S.Coname n), S.Negative_name (S.Coname m) -> String.equal n m
      | _, _ -> false
    ;;

    let empty_env = []

    let lookup_identifier env n =
      let rec aux stack n depth =
        match stack with
        | [] ->
          (match n with
           | S.Positive_name (S.Name n) -> FreeP n
           | S.Negative_name (S.Coname n) -> FreeC n)
        | n' :: stack' ->
          if neutral_name_match n n' then Bound depth else aux stack' n (depth + 1)
      in
      aux env n 0
    ;;

    let push_name v env = S.Positive_name v :: env
    let push_coname k env = S.Negative_name k :: env

    let rec convert_producer env p : producer =
      match p with
      | S.V name -> V (lookup_identifier env (S.Positive_name name))
      | S.Mu (k, cut) -> Mu (convert_cut (push_coname k env) cut)
      | S.Pair (a, b) -> Pair (convert_neutral env a, convert_neutral env b)
      | S.Cosplit (x, y, cut) ->
        if neutral_name_match x y
        then raise (Failure "Cosplit: name conflict in parameters")
        else (
          (* it is x first, then y, so that
           * x will be the first to be looked up (0)
           * then y (1) *)
          let env' = x :: y :: env in
          Cosplit (convert_cut env' cut))

    and convert_consumer env c : consumer =
      match c with
      | S.C coname -> C (lookup_identifier env (S.Negative_name coname))
      | S.MuTilde (v, cut) -> MuTilde (convert_cut (push_name v env) cut)
      | S.Split (x, y, cut) ->
        if neutral_name_match x y
        then raise (Failure "Split: name conflict in parameters")
        else (
          let env' = x :: y :: env in
          Split (convert_cut env' cut))
      | S.Copair (a, b) -> Copair (convert_neutral env a, convert_neutral env b)

    and convert_cut env cut : cut =
      { p = convert_producer env cut.p; c = convert_consumer env cut.c }

    and convert_neutral env neutral : neutral =
      match neutral with
      | S.Positive p -> Positive (convert_producer env p)
      | S.Negative c -> Negative (convert_consumer env c)
    ;;
  end

  let convert : Surface.t -> t = Converter.convert_cut Converter.empty_env

  let rec aequiv_producer (a : producer) (b : producer) =
    match a, b with
    | V (Bound n), V (Bound n') -> n = n'
    | V (FreeP n), V (FreeP n') -> String.equal n n'
    | V (FreeC _), _ -> assert false
    | _, V (FreeC _) -> assert false
    | Mu cut, Mu cut' -> aequiv_cut cut cut'
    | Pair (a, b), Pair (c, d) -> aequiv_neutral a c && aequiv_neutral b d
    | Cosplit cut, Cosplit cut' -> aequiv_cut cut cut'
    | _, _ -> false

  and aequiv_consumer (a : consumer) (b : consumer) =
    match a, b with
    | C (Bound n), C (Bound n') -> n = n'
    | C (FreeC n), C (FreeC n') -> String.equal n n'
    | C (FreeP _), _ -> assert false
    | _, C (FreeP _) -> assert false
    | MuTilde cut, MuTilde cut' -> aequiv_cut cut cut'
    | Split cut, Split cut' -> aequiv_cut cut cut'
    | Copair (a, b), Copair (c, d) -> aequiv_neutral a c && aequiv_neutral b d
    | _, _ -> false

  and aequiv_cut (a : cut) (b : cut) = aequiv_producer a.p b.p && aequiv_consumer a.c b.c

  and aequiv_neutral (a : neutral) (b : neutral) =
    match a, b with
    | Positive a, Positive b -> aequiv_producer a b
    | Negative a, Negative b -> aequiv_consumer a b
    | _, _ -> false
  ;;

  let aequiv = aequiv_cut
end
