open Ast.Core

(* Utilities for beta-reducing terms. 
 * ! this beta reducer assumes that all
 * bound variables are recursively dealt 
 * with accordingly - so you can't do something funny
 * like attempting to substitute a bound variable
 * into a bound variable. *)
module Beta_reducer : sig
  val beta_reduce_with_producer : int -> producer -> t -> (t, exn) result
  val beta_reduce_with_consumer : int -> consumer -> t -> (t, exn) result
end = struct
  module Utils = struct
    let binding_arity_producer p =
      match p with
      | V _ -> 0
      | Mu _ -> 1
      | Pair _ -> 0
      | Cosplit _ -> 2
    ;;

    let binding_arity_consumer c =
      match c with
      | C _ -> 0
      | MuTilde _ -> 1
      | Split _ -> 2
      | Copair _ -> 0
    ;;

    let shift_index_under_producer index producer =
      index + binding_arity_producer producer
    ;;

    let shift_index_under_consumer index consumer =
      index + binding_arity_consumer consumer
    ;;
  end

  let rec subst_producer_in_producer (index : int) (term : producer) (target : producer)
    : producer
    =
    let new_index = Utils.shift_index_under_producer index target in
    match target with
    | V (Bound n) when n = index -> term
    | V x -> V x
    | Mu cut -> Mu (subst_producer_in_cut new_index term cut)
    | Pair (a, b) ->
      Pair (subst_producer_in_neutral index term a, subst_producer_in_neutral index term b)
    | Cosplit cut -> Cosplit (subst_producer_in_cut new_index term cut)

  and subst_producer_in_consumer (index : int) (term : producer) (target : consumer)
    : consumer
    =
    let new_index = Utils.shift_index_under_consumer index target in
    match target with
    | C (Bound n) when n = index ->
      raise (Failure "Type error: a producer is being used as a consumer!")
    | C x -> C x
    | MuTilde cut -> MuTilde (subst_producer_in_cut new_index term cut)
    | Split cut -> Split (subst_producer_in_cut new_index term cut)
    | Copair (a, b) ->
      Copair
        (subst_producer_in_neutral index term a, subst_producer_in_neutral index term b)

  and subst_producer_in_cut (index : int) (term : producer) (target : cut) : cut =
    { p = subst_producer_in_producer index term target.p
    ; c = subst_producer_in_consumer index term target.c
    }

  and subst_producer_in_neutral (index : int) (term : producer) (target : neutral)
    : neutral
    =
    match target with
    | Positive p -> Positive (subst_producer_in_producer index term p)
    | Negative c -> Negative (subst_producer_in_consumer index term c)
  ;;

  let rec subst_consumer_in_producer (index : int) (term : consumer) (target : producer)
    : producer
    =
    let new_index = Utils.shift_index_under_producer index target in
    match target with
    | V (Bound n) when n = index ->
      raise (Failure "Type error: a consumer is being used as a producer!")
    | V x -> V x
    | Mu cut -> Mu (subst_consumer_in_cut new_index term cut)
    | Pair (a, b) ->
      Pair (subst_consumer_in_neutral index term a, subst_consumer_in_neutral index term b)
    | Cosplit cut -> Cosplit (subst_consumer_in_cut new_index term cut)

  and subst_consumer_in_consumer (index : int) (term : consumer) (target : consumer)
    : consumer
    =
    let new_index = Utils.shift_index_under_consumer index target in
    match target with
    | C (Bound n) -> if n = index then term else C (Bound n)
    | C x -> C x
    | MuTilde cut -> MuTilde (subst_consumer_in_cut new_index term cut)
    | Split cut -> Split (subst_consumer_in_cut new_index term cut)
    | Copair (a, b) ->
      Copair
        (subst_consumer_in_neutral index term a, subst_consumer_in_neutral index term b)

  and subst_consumer_in_cut (index : int) (term : consumer) (target : cut) : cut =
    { p = subst_consumer_in_producer index term target.p
    ; c = subst_consumer_in_consumer index term target.c
    }

  and subst_consumer_in_neutral (index : int) (term : consumer) (target : neutral)
    : neutral
    =
    match target with
    | Positive p -> Positive (subst_consumer_in_producer index term p)
    | Negative c -> Negative (subst_consumer_in_consumer index term c)
  ;;

  (* safe entrypoints *)
  let beta_reduce_with_producer (index : int) (term : producer) (target : t)
    : (t, exn) result
    =
    match term with
    | V (Bound _) -> Error (Failure "attempted to substitute a bound variable")
    | term -> Ok (subst_producer_in_cut index term target)
  ;;

  let beta_reduce_with_consumer (index : int) (term : consumer) (target : t)
    : (t, exn) result
    =
    match term with
    | C (Bound _) -> Error (Failure "attempted to substitute a bound variable")
    | term -> Ok (subst_consumer_in_cut index term target)
  ;;
end

module type RUNNER = sig
  type step =
    | Incomplete of t
    | Complete of t

  val step_once : t -> step
  val eval : t -> t
end

module Call_by_value : RUNNER = struct
  type step =
    | Incomplete of t
    | Complete of t

  let rec step_once t = Complete t
  let eval t = raise (Failure "Not_implemented")
end

module Call_by_name : RUNNER = struct
  type step =
    | Incomplete of t
    | Complete of t

  let rec step_once t = Complete t
  let eval t = raise (Failure "Not_implemented")
end
