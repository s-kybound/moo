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
  let beta_reduce_with_producer (index : int) (term : producer) (target : cut)
    : (cut, exn) result
    =
    match term with
    | V (Bound _) -> Error (Failure "attempted to substitute a bound variable")
    | term -> Ok (subst_producer_in_cut index term target)
  ;;

  let beta_reduce_with_consumer (index : int) (term : consumer) (target : cut)
    : (cut, exn) result
    =
    match term with
    | C (Bound _) -> Error (Failure "attempted to substitute a bound variable")
    | term -> Ok (subst_consumer_in_cut index term target)
  ;;

  let beta_reduce_with_neutral (index : int) (term : neutral) (target : cut)
    : (cut, exn) result
    =
    match term with
    | Positive p -> beta_reduce_with_producer index p target
    | Negative c -> beta_reduce_with_consumer index c target
  ;;
end

module Env = struct
  type element =
    | Producer of producer
    | Consumer of consumer

  type t = (identifier, element) Hashtbl.t

  let empty_env : t = Hashtbl.create 10
  let is_defined i (t : t) = Hashtbl.mem t i

  let get_consumer i (t : t) =
    match Hashtbl.find_opt t i with
    | None -> failwith "not_found"
    | Some e ->
      (match e with
       | Consumer c -> c
       | Producer _ -> failwith "attempted to get consumer, this is a producer")
  ;;

  let get_producer i (t : t) =
    match Hashtbl.find_opt t i with
    | None -> failwith "not_found"
    | Some e ->
      (match e with
       | Producer p -> p
       | Consumer _ -> failwith "attempted to get producer, this is a consumer")
  ;;

  module Substituter = struct
    let rec substitute_producer env p =
      match p with
      | V name when is_defined name env -> get_producer name env
      | V id -> V id
      | Mu cut -> Mu (substitute_cut env cut)
      | Pair (a, b) -> Pair (substitute_neutral env a, substitute_neutral env b)
      | Cosplit cut -> Cosplit (substitute_cut env cut)

    and substitute_consumer env c =
      match c with
      | C name when is_defined name env -> get_consumer name env
      | C id -> C id
      | MuTilde cut -> MuTilde (substitute_cut env cut)
      | Split cut -> Split (substitute_cut env cut)
      | Copair (a, b) -> Copair (substitute_neutral env a, substitute_neutral env b)

    and substitute_cut env cut =
      { p = substitute_producer env cut.p; c = substitute_consumer env cut.c }

    and substitute_neutral env n =
      match n with
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
           Hashtbl.replace t n (Producer p)
         | Consumer (cn, c) ->
           let c = Substituter.substitute_consumer t c in
           Hashtbl.replace t cn (Consumer c))
      program.definitions
  ;;
end

module type RUNNER = sig
  type step =
    | Incomplete of cut
    | Complete of cut
    | Error of exn

  val name : string
  val step_once : Env.t -> cut -> step
  val eval : Env.t -> t -> cut
end

module Call_by_value : RUNNER = struct
  type step =
    | Incomplete of cut
    | Complete of cut
    | Error of exn

  let name = "call-by-value"

  (* the value judgement, on producers. 
   * only used to analyze producers already at a
   * top-level cut-the cut that is already being
   * evaluated. so no bound variables.
  *)
  let rec is_val (p : producer) : bool =
    let is_val_neutral n =
      match n with
      | Negative _ -> true (* any consumer is a value. *)
      | Positive p -> is_val p
    in
    match p with
    | V (FreeP _) -> true
    | V (FreeC _) -> assert false
    | V (Bound _) -> assert false
    | Mu _ -> false
    | Pair (a, b) -> is_val_neutral a && is_val_neutral b
    | Cosplit _ -> true
  ;;

  let step_once env t =
    match t.p, t.c with
    (* encode impossible cases - ill formatted names *)
    | V (FreeC _), _ -> Error (Failure "encountered consumer name in producer position")
    | _, C (FreeP _) -> Error (Failure "encountered producer name in consumer position")
    (* encode namespacing errors - V and C must only have free variables *)
    | V (Bound _), _ ->
      Error
        (Failure
           "encountered bound variable in producer - should have been beta-eliminated")
    | _, C (Bound _) ->
      Error
        (Failure
           "encountered bound variable in consumer - should have been beta-eliminated")
    (* encode type errors *)
    | Pair _, Copair _ -> Error (Failure "type error: A*B producer, C&D consumer")
    | Cosplit _, Split _ -> Error (Failure "type error: A&B producer, C*D consumer")
    (* environment lookup *)
    | V n, c when Env.is_defined n env -> Incomplete { p = Env.get_producer n env; c }
    | p, C cn when Env.is_defined cn env && is_val p ->
      Incomplete { p; c = Env.get_consumer cn env }
    (* consider "unable to progress" cases as complete - if these names were substituted 
     * can continue in the future *)
    | V _, Split _ -> Complete t
    (* end cases *)
    | V _, C _ -> Complete t
    | Cosplit _, C _ -> Complete t
    | (Pair _ as p), C _ when is_val p -> Complete t
    (* call-by-value semantics *)
    (* any letcc is immediately evaluated *)
    | Mu cut, c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* let is only evaluated when the producer is a value *)
    | (V _ as p), MuTilde cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | (Cosplit _ as p), MuTilde cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | (Pair _ as p), MuTilde cut when is_val p ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* pair semantics *)
    | Pair (a, b), Split cut when is_val (Pair (a, b)) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* the rest of the pairs below are NOT values. 
     * these rules equate to the
     * pair dynamic focusing rules *)
    | Pair (Positive a, Positive b), cons when is_val a ->
      let new_producer = b in
      let new_consumer =
        MuTilde { p = Pair (Positive a, Positive (V (Bound 0))); c = cons }
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (Negative a, Positive b), cons ->
      let new_producer = b in
      let new_consumer =
        MuTilde { p = Pair (Negative a, Positive (V (Bound 0))); c = cons }
      in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (Positive a, b), cons ->
      let new_producer = a in
      let new_consumer = MuTilde { p = Pair (Positive (V (Bound 0)), b); c = cons } in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (Negative _, Negative _), _ -> assert false (* value, handled already *)
    (* cosplit semantics - once the producer is a val,
     * and we have already assured that it is, 
     * simplify the elements in the copair if it can be done
     * i was really hoping to not use not is_val, 
     * may need a round of simplification in the future. *)
    | p, Copair (Positive a, b) when not (is_val a) ->
      let new_producer = a in
      let new_consumer = MuTilde { p; c = Copair (Positive (V (Bound 0)), b) } in
      Incomplete { p = new_producer; c = new_consumer }
    | p, Copair (a, Positive b) when not (is_val b) ->
      let new_producer = b in
      let new_consumer = MuTilde { p; c = Copair (a, Positive (V (Bound 0))) } in
      Incomplete { p = new_producer; c = new_consumer }
    | V _, Copair _ -> Complete t
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

  let eval env t =
    Env.load_definitions t env;
    let rec step_through cut =
      match step_once env cut with
      | Complete cut -> cut
      | Incomplete cut -> step_through cut
      | Error exn -> raise exn
    in
    step_through t.main
  ;;
end

module Call_by_name : RUNNER = struct
  type step =
    | Incomplete of cut
    | Complete of cut
    | Error of exn

  let name = "call-by-name"

  (* the covalue judgement, on consumers. 
   * only used to analyze consumers already at a
   * top-level cut-the cut that is already being
   * evaluated. so no bound variables.
  *)
  let rec is_coval (c : consumer) : bool =
    let is_coval_neutral n =
      match n with
      | Positive _ -> true (* any producer is a covalue. *)
      | Negative c -> is_coval c
    in
    match c with
    | C (FreeC _) -> true
    | C (FreeP _) -> assert false
    | C (Bound _) -> assert false
    | MuTilde _ -> false
    | Copair (a, b) -> is_coval_neutral a && is_coval_neutral b
    | Split _ -> true
  ;;

  let step_once env t =
    match t.p, t.c with
    (* encode impossible cases - ill formatted names *)
    | V (FreeC _), _ -> Error (Failure "encountered consumer name in producer position")
    | _, C (FreeP _) -> Error (Failure "encountered producer name in consumer position")
    (* encode namespacing errors - V and C must only have free variables *)
    | V (Bound _), _ ->
      Error
        (Failure
           "encountered bound variable in producer - should have been beta-eliminated")
    | _, C (Bound _) ->
      Error
        (Failure
           "encountered bound variable in consumer - should have been beta-eliminated")
    (* encode type errors *)
    | Pair _, Copair _ -> Error (Failure "type error: A*B producer, C&D consumer")
    | Cosplit _, Split _ -> Error (Failure "type error: A&B producer, C*D consumer")
    (* environment lookup *)
    | p, C cn when Env.is_defined cn env -> Incomplete { p; c = Env.get_consumer cn env }
    | V n, c when Env.is_defined n env && is_coval c ->
      Incomplete { p = Env.get_producer n env; c }
    (* consider "unable to progress" cases as complete - if these names were substituted 
     * can continue in the future *)
    | Cosplit _, C _ -> Complete t
    (* TODO: end cases *)
    | V _, C _ -> Complete t
    | V _, Split _ -> Complete t
    | V _, (Copair _ as c) when is_coval c -> Complete t
    (* call-by-name semantics *)
    (* any let is immediately evaluated *)
    | p, MuTilde cut ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* letcc is only evaluated when the consumer is a covalue *)
    | Mu cut, (C _ as c) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | Mu cut, (Split _ as c) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | Mu cut, (Copair _ as c) when is_coval c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* copair semantics *)
    | Cosplit cut, Copair (a, b) when is_coval (Copair (a, b)) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 a cut)
        ~ok:(fun cut ->
          Result.fold
            (Beta_reducer.beta_reduce_with_neutral 1 b cut)
            ~ok:(fun cut -> Incomplete cut)
            ~error:(fun exn -> Error exn))
        ~error:(fun exn -> Error exn)
    (* the rest of the copairs below are NOT covalues. 
     * these rules equate to the
     * copair dynamic focusing rules *)
    | prod, Copair (Negative a, Negative b) when is_coval a ->
      let new_consumer = b in
      let new_producer =
        Mu { c = Copair (Negative a, Negative (C (Bound 0))); p = prod }
      in
      Incomplete { p = new_producer; c = new_consumer }
    | prod, Copair (Positive a, Negative b) ->
      let new_consumer = b in
      let new_producer =
        Mu { c = Copair (Positive a, Negative (C (Bound 0))); p = prod }
      in
      Incomplete { p = new_producer; c = new_consumer }
    | prod, Copair (Negative a, b) ->
      let new_consumer = a in
      let new_producer = Mu { c = Copair (Negative (C (Bound 0)), b); p = prod } in
      Incomplete { p = new_producer; c = new_consumer }
    | _, Copair (Positive _, Positive _) -> assert false (* covalue, handled already *)
    (* split semantics - once the consumer is a coval,
     * and we have already assured that it is, 
     * simplify the elements in the pair if it can be done
     * i was really hoping to not use not is_val, 
     * may need a round of simplification in the future. *)
    | Pair (Negative a, b), c when not (is_coval a) ->
      let new_producer = Mu { c; p = Pair (Negative (C (Bound 0)), b) } in
      let new_consumer = a in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair (a, Negative b), c when not (is_coval b) ->
      let new_producer = Mu { c; p = Pair (a, Negative (C (Bound 0))) } in
      let new_consumer = b in
      Incomplete { p = new_producer; c = new_consumer }
    | Pair _, C _ -> Complete t
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

  let eval env t =
    Env.load_definitions t env;
    let rec step_through t =
      match step_once env t with
      | Complete t -> t
      | Incomplete t -> step_through t
      | Error exn -> raise exn
    in
    step_through t.main
  ;;
end
