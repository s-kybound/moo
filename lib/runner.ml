open Ast.Core

(* Utilities for beta-reducing terms. 
 * ! this beta reducer assumes that all
 * bound variables are recursively dealt 
 * with accordingly - so you can't do something funny
 * like attempting to substitute a bound variable
 * into a bound variable. *)
module Beta_reducer : sig
  val beta_reduce_with_producer : int -> producer -> cut -> (cut, exn) result
  val beta_reduce_with_consumer : int -> consumer -> cut -> (cut, exn) result
  val beta_reduce_with_neutral : int -> neutral -> cut -> (cut, exn) result
end = struct
  module Utils = struct
    let binding_arity_producer p =
      match p with
      | Mu _ -> 1
      | Pair _ -> 0
      | Cosplit _ -> 2
      | Unit -> 0
      | Codo _ -> 0
    ;;

    let binding_arity_consumer c =
      match c with
      | MuTilde _ -> 1
      | Split _ -> 2
      | Copair _ -> 0
      | Counit -> 0
      | Do _ -> 0
    ;;

    let shift_index_under_producer index producer =
      index + binding_arity_producer producer
    ;;

    let shift_index_under_consumer index consumer =
      index + binding_arity_consumer consumer
    ;;
  end

  let rec subst_neutral_in_producer (index : int) (term : neutral) (target : producer)
    : producer
    =
    let new_index = Utils.shift_index_under_producer index target in
    match target with
    | Mu cut -> Mu (subst_neutral_in_cut new_index term cut)
    | Pair (a, b) ->
      Pair (subst_neutral_in_neutral index term a, subst_neutral_in_neutral index term b)
    | Cosplit cut -> Cosplit (subst_neutral_in_cut new_index term cut)
    | Unit -> Unit
    | Codo cut -> Codo (subst_neutral_in_cut new_index term cut)

  and subst_neutral_in_consumer (index : int) (term : neutral) (target : consumer)
    : consumer
    =
    let new_index = Utils.shift_index_under_consumer index target in
    match target with
    | MuTilde cut -> MuTilde (subst_neutral_in_cut new_index term cut)
    | Split cut -> Split (subst_neutral_in_cut new_index term cut)
    | Copair (a, b) ->
      Copair (subst_neutral_in_neutral index term a, subst_neutral_in_neutral index term b)
    | Counit -> Counit
    | Do cut -> Do (subst_neutral_in_cut new_index term cut)

  and subst_neutral_in_cut (index : int) (term : neutral) (target : cut) : cut =
    { p = subst_neutral_in_neutral index term target.p
    ; c = subst_neutral_in_neutral index term target.c
    }

  and subst_neutral_in_neutral (index : int) (term : neutral) (target : neutral) : neutral
    =
    match target with
    | Name (Bound n) when n = index -> term
    | Name x -> Name x
    | Positive p -> Positive (subst_neutral_in_producer index term p)
    | Negative c -> Negative (subst_neutral_in_consumer index term c)
  ;;

  (* safe entrypoints *)
  let beta_reduce_with_producer (index : int) (term : producer) (target : cut)
    : (cut, exn) result
    =
    Ok (subst_neutral_in_cut index (Positive term) target)
  ;;

  let beta_reduce_with_consumer (index : int) (term : consumer) (target : cut)
    : (cut, exn) result
    =
    Ok (subst_neutral_in_cut index (Negative term) target)
  ;;

  let beta_reduce_with_neutral (index : int) (term : neutral) (target : cut)
    : (cut, exn) result
    =
    match term with
    | Name (Bound _) -> Error (Failure "attempted to substitute a bound variable")
    | term -> Ok (subst_neutral_in_cut index term target)
  ;;
end

module Env = struct
  type t = (string, neutral) Hashtbl.t

  let empty_env () : t = Hashtbl.create 10
  let is_defined i (t : t) = Hashtbl.mem t i

  let get_neutral i (t : t) =
    match Hashtbl.find_opt t i with
    | None -> failwith "not_found"
    | Some e -> e
  ;;

  module Substituter = struct
    let rec substitute_producer env p =
      match p with
      | Mu cut -> Mu (substitute_cut env cut)
      | Pair (a, b) -> Pair (substitute_neutral env a, substitute_neutral env b)
      | Cosplit cut -> Cosplit (substitute_cut env cut)
      | Unit -> Unit
      | Codo cut -> Codo (substitute_cut env cut)

    and substitute_consumer env c =
      match c with
      | MuTilde cut -> MuTilde (substitute_cut env cut)
      | Split cut -> Split (substitute_cut env cut)
      | Copair (a, b) -> Copair (substitute_neutral env a, substitute_neutral env b)
      | Counit -> Counit
      | Do cut -> Do (substitute_cut env cut)

    and substitute_cut env cut =
      { p = substitute_neutral env cut.p; c = substitute_neutral env cut.c }

    and substitute_neutral env n =
      match n with
      | Name (Free name) when is_defined name env -> get_neutral name env
      | Name x -> Name x
      | Positive p -> Positive (substitute_producer env p)
      | Negative c -> Negative (substitute_consumer env c)
    ;;
  end

  let load_definitions program t =
    List.iter
      (fun (d : definition) ->
         match d with
         (*
            no recursive names yet
         | Producer_rec (n, p) ->
         | Consumer_rec (cn, c) ->
         *)
         | Producer (n, p) ->
           let p = Substituter.substitute_producer t p in
           Hashtbl.replace t n (Positive p)
         | Consumer (cn, c) ->
           let c = Substituter.substitute_consumer t c in
           Hashtbl.replace t cn (Negative c))
      program.definitions
  ;;

  let substitute_definitions cut t = Substituter.substitute_cut t cut
end

module type JUDGEMENTS = sig
  val name : string

  (** the value judgement on producers *)
  val is_val : Ast.Core.producer -> bool

  (** the covalue judgement on consumers *)
  val is_coval : Ast.Core.consumer -> bool
end

module type EVALUATION_STRATEGY = sig
  (** a single step, corresponding to a step of small-step semantics *)
  type step =
    | Incomplete of cut
    | Complete of cut
    | Error of exn

  val name : string
  val step_once : cut -> step

  (** steps a program through to completion within an environment *)
  val eval : Env.t -> t -> cut
end

(* Lazy judgements only care if the value is in computable shape.
 * otherwise it does whatever it wants. *)
module Lazy : JUDGEMENTS = struct
  let name = "lazy"

  let is_val (p : producer) : bool =
    match p with
    | Mu _ -> false
    | Pair _ -> true
    | Cosplit _ -> true
    | Unit -> true
    | Codo _ -> true
  ;;

  let is_coval (c : consumer) : bool =
    match c with
    | MuTilde _ -> false
    | Copair _ -> true
    | Split _ -> true
    | Counit -> true
    | Do _ -> true
  ;;
end

(* eager judgements ensure that all values/covalues within
 * a constructor are in principal form before evaluating on it. 
 * in CBV, this also includes the covalue judgement, and same 
 * for CBN and value judgement. *)
module Eager : JUDGEMENTS = struct
  let name = "eager"

  let rec is_val (p : producer) : bool =
    let is_val_neutral n =
      match n with
      | Name (Free _) -> true
      | Name (Bound _) -> assert false
      | Negative c -> is_coval c
      | Positive p -> is_val p
    in
    match p with
    | Mu _ -> false
    | Pair (a, b) -> is_val_neutral a && is_val_neutral b
    | Cosplit _ -> true
    | Unit -> true
    | Codo _ -> true

  and is_coval (c : consumer) : bool =
    let is_coval_neutral n =
      match n with
      | Name (Free _) -> true
      | Name (Bound _) -> assert false
      | Positive p -> is_val p
      | Negative c -> is_coval c
    in
    match c with
    | MuTilde _ -> false
    | Copair (a, b) -> is_coval_neutral a && is_coval_neutral b
    | Split _ -> true
    | Counit -> true
    | Do _ -> true
  ;;
end

module Make_CBV (J : JUDGEMENTS) : EVALUATION_STRATEGY = struct
  type step =
    | Incomplete of cut
    | Complete of cut
    | Error of exn

  let name = Printf.sprintf "%s-call-by-value" J.name
  let is_val = J.is_val
  let is_coval = J.is_coval

  let producer_consumer_step p c =
    match p, c with
    (* encode type errors *)
    | Pair _, Copair _ -> Error (Failure "type error: A*B producer, C&D consumer")
    | Pair _, Counit -> Error (Failure "type error: A*B producer, counit consumer")
    | Pair _, Do _ -> Error (Failure "type error: A*B producer, unit consumer")
    | Cosplit _, Split _ -> Error (Failure "type error: A&B producer, C*D consumer")
    | Cosplit _, Counit -> Error (Failure "type error: A&B producer, counit consumer")
    | Cosplit _, Do _ -> Error (Failure "type error: A&B producer, unit consumer")
    | Unit, Copair _ -> Error (Failure "type error; unit producer, A&B consumer")
    | Unit, Split _ -> Error (Failure "type error; unit producer, A*B consumer")
    | Unit, Counit -> Error (Failure "type error; unit producer, counit consumer")
    | Codo _, Copair _ -> Error (Failure "type error: counit producer, A&B consumer")
    | Codo _, Split _ -> Error (Failure "type error: counit producer, A*B consumer")
    | Codo _, Do _ -> Error (Failure "type error: counit producer, unit consumer")
    (* any letcc is immediately evaluated *)
    | Mu cut, c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* any let is evaluated when the right is a covalue *)
    | p, MuTilde cut when is_val p ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* unit semantics *)
    | Unit, Do cut -> Incomplete cut
    (* counit semantics *)
    | Codo cut, Counit -> Incomplete cut
    (* pair semantics *)
    (* pair destruction *)
    | Pair (a, b), Split cut when is_val (Pair (a, b)) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* pair focusing rules, left to right *)
    | Pair (Positive a, b), cons when not (is_val a) ->
      let new_producer = Positive a in
      let new_consumer =
        let pair = Pair (Name (Bound 0), b) in
        Negative (MuTilde { p = Positive pair; c = Negative cons })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (Negative a, b), cons when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let pair = Pair (Name (Bound 0), b) in
        Positive (Mu { p = Positive pair; c = Negative cons })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (a, Positive b), cons when not (is_val b) ->
      let new_producer = Positive b in
      let new_consumer =
        let pair = Pair (a, Name (Bound 0)) in
        Negative (MuTilde { p = Positive pair; c = Negative cons })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (a, Negative b), cons when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let pair = Pair (a, Name (Bound 0)) in
        Positive (Mu { p = Positive pair; c = Negative cons })
      in
      Incomplete { p = new_producer; c = new_consumer }
    (* any pair below is already a value.
     * and since the only non_value was mu
     * and it has already been dealt with,
     * ANYTHING here is a value. *)
    (* catch-all pair destruction in case the
     * is_val judgement is ill-formed *)
    | Pair (a, b), Split cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* catchall for any value and mutilde *)
    | p, MuTilde cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* copair semantics - any potential simplification is only done
     * when the left side is completely simplified. *)
    (* copair destruction *)
    | Cosplit cut, Copair (a, b) when is_coval (Copair (a, b)) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* copair focusing rules, left to right *)
    | prod, Copair (Positive a, b) when not (is_val a) ->
      let new_producer = Positive a in
      let new_consumer =
        let copair = Copair (Name (Bound 0), b) in
        Negative (MuTilde { p = Positive prod; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | prod, Copair (Negative a, b) when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let copair = Copair (Name (Bound 0), b) in
        Positive (Mu { c = Negative copair; p = Positive prod })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | prod, Copair (a, Positive b) when not (is_val b) ->
      let new_producer = Positive b in
      let new_consumer =
        let copair = Copair (a, Name (Bound 0)) in
        Negative (MuTilde { p = Positive prod; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | prod, Copair (a, Negative b) when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let copair = Copair (a, Name (Bound 0)) in
        Positive (Mu { c = Negative copair; p = Positive prod })
      in
      Incomplete { p = new_producer; c = new_consumer }
    (* catch-all copair destruction in case the
     * is_val judgement is ill-formed *)
    | Cosplit cut, Copair (a, b) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
  ;;

  let producer_name_step p n =
    let consumer = Name (Free n) in
    match p with
    | Mu cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 consumer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | p when is_val p ->
      let cut = { p = Positive p; c = consumer } in
      Complete cut
    | Pair (Positive a, b) when not (is_val a) ->
      let new_producer = Positive a in
      let new_consumer =
        let pair = Pair (Name (Bound 0), b) in
        Negative (MuTilde { p = Positive pair; c = consumer })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (Negative a, b) when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let pair = Pair (Name (Bound 0), b) in
        Positive (Mu { p = Positive pair; c = consumer })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (a, Positive b) when not (is_val b) ->
      let new_producer = Positive b in
      let new_consumer =
        let pair = Pair (a, Name (Bound 0)) in
        Negative (MuTilde { p = Positive pair; c = consumer })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (a, Negative b) when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let pair = Pair (a, Name (Bound 0)) in
        Positive (Mu { p = Positive pair; c = consumer })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | p ->
      let cut = { p = Positive p; c = consumer } in
      Complete cut
  ;;

  let name_consumer_step n c =
    let producer = Name (Free n) in
    match c with
    | MuTilde cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 producer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | Copair (a, b) when is_coval (Copair (a, b)) ->
      let cut = { p = producer; c = Negative c } in
      Complete cut
    | Copair (Positive a, b) when not (is_val a) ->
      let new_producer = Positive a in
      let new_consumer =
        let copair = Copair (Name (Bound 0), b) in
        Negative (MuTilde { p = producer; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Copair (Negative a, b) when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let copair = Copair (Name (Bound 0), b) in
        Positive (Mu { p = producer; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Copair (a, Positive b) when not (is_val b) ->
      let new_producer = Positive b in
      let new_consumer =
        let copair = Copair (a, Name (Bound 0)) in
        Negative (MuTilde { p = producer; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Copair (a, Negative b) when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let copair = Copair (a, Name (Bound 0)) in
        Positive (Mu { p = producer; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | c ->
      let cut = { p = producer; c = Negative c } in
      Complete cut
  ;;

  let step_once cut =
    (* this is necessary to allow types such as
     * (fun a a) to accept both positive and negative
     * parameters in the future *)
    let normalize cut =
      match cut.p, cut.c with
      | c, Positive p -> { p = Positive p; c }
      | Negative n, p -> { p; c = Negative n }
      | _ -> cut
    in
    let cut = normalize cut in
    match cut.p, cut.c with
    (* invalid steps *)
    | Name (Bound _), _ ->
      failwith "encountered bound variable in producer - should have been beta-eliminated"
    | _, Name (Bound _) ->
      failwith "encountered bound variable in consumer - should have been beta-eliminated"
    (* these are the states we are hoping typechecking will prevent *)
    | Negative _, _ -> failwith "encountered a consumer in producer position!"
    | _, Positive _ -> failwith "encountered a producer in consumer position!"
    (* these are the actual imprrtant steps *)
    | Positive p, Negative c -> producer_consumer_step p c
    | Positive p, Name (Free n) -> producer_name_step p n
    | Name (Free n), Negative c -> name_consumer_step n c
    | Name (Free _), Name (Free _) -> Complete cut
  ;;

  let eval env t =
    Env.load_definitions t env;
    let rec step_through cut =
      match step_once cut with
      | Complete cut -> cut
      | Incomplete cut -> step_through cut
      | Error exn -> raise exn
    in
    let prepared_program = Env.substitute_definitions t.main env in
    step_through prepared_program
  ;;
end

module Make_CBN (J : JUDGEMENTS) : EVALUATION_STRATEGY = struct
  type step =
    | Incomplete of cut
    | Complete of cut
    | Error of exn

  let name = Printf.sprintf "%s-call-by-name" J.name
  let is_coval = J.is_coval

  let producer_consumer_step p c =
    match p, c with
    (* encode type errors *)
    | Pair _, Copair _ -> Error (Failure "type error: A*B producer, C&D consumer")
    | Pair _, Counit -> Error (Failure "type error: A*B producer, counit consumer")
    | Pair _, Do _ -> Error (Failure "type error: A*B producer, unit consumer")
    | Cosplit _, Split _ -> Error (Failure "type error: A&B producer, C*D consumer")
    | Cosplit _, Counit -> Error (Failure "type error: A&B producer, counit consumer")
    | Cosplit _, Do _ -> Error (Failure "type error: A&B producer, unit consumer")
    | Unit, Copair _ -> Error (Failure "type error; unit producer, A&B consumer")
    | Unit, Split _ -> Error (Failure "type error; unit producer, A*B consumer")
    | Unit, Counit -> Error (Failure "type error; unit producer, counit consumer")
    | Codo _, Copair _ -> Error (Failure "type error: counit producer, A&B consumer")
    | Codo _, Split _ -> Error (Failure "type error: counit producer, A*B consumer")
    | Codo _, Do _ -> Error (Failure "type error: counit producer, unit consumer")
    (* any let is immediately evaluated *)
    | p, MuTilde cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* any letcc is evaluated when the right is a covalue *)
    | Mu cut, c when is_coval c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* counit semantics *)
    | Codo cut, Counit -> Incomplete cut
    (* unit semantics *)
    | Unit, Do cut -> Incomplete cut
    (* copair semantics *)
    (* canonical copair destruction *)
    | Cosplit cut, Copair (a, b) when is_coval (Copair (a, b)) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* copair focusing rules, left to right *)
    | prod, Copair (Negative a, b) when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let copair = Copair (Name (Bound 0), b) in
        Positive (Mu { c = Negative copair; p = Positive prod })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | prod, Copair (a, Negative b) when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let copair = Copair (a, Name (Bound 0)) in
        Positive (Mu { c = Negative copair; p = Positive prod })
      in
      Incomplete { p = new_producer; c = new_consumer }
    (* any copair below is already a covalue.
     * and since the only non_covalue was mutilde
     * and it has already been dealt with,
     * ANYTHING here is a covalue. *)
    (* catch-all copair destruction in case the
     * is_coval judgement is ill-formed *)
    | Cosplit cut, Copair (a, b) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* catchall for any covalue and mu *)
    | Mu cut, c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* pair semantics - any potential simplification is only done
     * when the right side is completely simplified. in order to treat
     * the pair using is_coval, we pretend it is a copair *)
    | Pair (a, b), Split cut when is_coval (Copair (a, b)) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* pair focusing rules, left to right *)
    | Pair (Negative a, b), cons when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let pair = Pair (Name (Bound 0), b) in
        Positive (Mu { c = Negative cons; p = Positive pair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (a, Negative b), cons when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let pair = Pair (a, Name (Bound 0)) in
        Positive (Mu { c = Negative cons; p = Positive pair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    (* catch-all pair destruction in case the
     * is_val judgement is ill-formed *)
    | Pair (a, b), Split cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
  ;;

  let producer_name_step p n =
    let consumer = Name (Free n) in
    match p with
    | Mu cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 consumer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | Pair (a, b) when is_coval (Copair (a, b)) ->
      let cut = { p = Positive p; c = consumer } in
      Complete cut
    | Pair (Negative a, b) when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let pair = Pair (Name (Bound 0), b) in
        Positive (Mu { p = Positive pair; c = consumer })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (a, Negative b) when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let pair = Pair (a, Name (Bound 0)) in
        Positive (Mu { p = Positive pair; c = consumer })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | p ->
      let cut = { p = Positive p; c = consumer } in
      Complete cut
  ;;

  let name_consumer_step n c =
    let producer = Name (Free n) in
    match c with
    | MuTilde cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 producer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | c when is_coval c ->
      let cut = { p = producer; c = Negative c } in
      Complete cut
    | Copair (Negative a, b) when not (is_coval a) ->
      let new_consumer = Negative a in
      let new_producer =
        let copair = Copair (Name (Bound 0), b) in
        Positive (Mu { p = producer; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Copair (a, Negative b) when not (is_coval b) ->
      let new_consumer = Negative b in
      let new_producer =
        let copair = Copair (a, Name (Bound 0)) in
        Positive (Mu { p = producer; c = Negative copair })
      in
      Incomplete { p = new_producer; c = new_consumer }
    | c ->
      let cut = { p = producer; c = Negative c } in
      Complete cut
  ;;

  let step_once cut =
    (* this is necessary to allow types such as
     * (fun a a) to accept both positive and negative
     * parameters in the future *)
    let normalize cut =
      match cut.p, cut.c with
      | c, Positive p -> { p = Positive p; c }
      | Negative n, p -> { p; c = Negative n }
      | _ -> cut
    in
    let cut = normalize cut in
    match cut.p, cut.c with
    (* invalid steps *)
    | Name (Bound _), _ ->
      failwith "encountered bound variable in producer - should have been beta-eliminated"
    | _, Name (Bound _) ->
      failwith "encountered bound variable in consumer - should have been beta-eliminated"
    (* these are the states we are hoping typechecking will prevent *)
    | Negative _, _ -> failwith "encountered a consumer in producer position!"
    | _, Positive _ -> failwith "encountered a producer in consumer position!"
    (* these are the actual imprrtant steps *)
    | Positive p, Negative c -> producer_consumer_step p c
    | Positive p, Name (Free n) -> producer_name_step p n
    | Name (Free n), Negative c -> name_consumer_step n c
    | Name (Free _), Name (Free _) -> Complete cut
  ;;

  let eval env t =
    Env.load_definitions t env;
    let rec step_through t =
      match step_once t with
      | Complete t -> t
      | Incomplete t -> step_through t
      | Error exn -> raise exn
    in
    let prepared_program = Env.substitute_definitions t.main env in
    step_through prepared_program
  ;;
end
