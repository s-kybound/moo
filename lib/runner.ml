open Ast
open Core

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
      | Tuple _ -> 0
      | Cosplit (_, binders) -> List.length binders
    ;;

    let binding_arity_consumer c =
      match c with
      | MuTilde _ -> 1
      | Split (_, binders) -> List.length binders
      | Cotuple _ -> 0
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
    | Mu (cut, typ) -> Mu (subst_neutral_in_cut new_index term cut, typ)
    | Tuple xs -> Tuple (List.map (subst_neutral_in_neutral index term) xs)
    | Cosplit (cut, typs) -> Cosplit (subst_neutral_in_cut new_index term cut, typs)

  and subst_neutral_in_consumer (index : int) (term : neutral) (target : consumer)
    : consumer
    =
    let new_index = Utils.shift_index_under_consumer index target in
    match target with
    | MuTilde (cut, typ) -> MuTilde (subst_neutral_in_cut new_index term cut, typ)
    | Split (cut, typs) -> Split (subst_neutral_in_cut new_index term cut, typs)
    | Cotuple xs -> Cotuple (List.map (subst_neutral_in_neutral index term) xs)

  and subst_neutral_in_cut (index : int) (term : neutral) (target : cut) : cut =
    { p = subst_neutral_in_neutral index term target.p
    ; c = subst_neutral_in_neutral index term target.c
    }

  and subst_neutral_in_neutral (index : int) (term : neutral) (target : neutral) : neutral
    =
    match target with
    | Name (Bound (n, _)) when n = index -> term
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

module Lazy : JUDGEMENTS = struct
  let name = "lazy"

  let is_val (p : producer) : bool =
    match p with
    | Mu _ -> false
    | Tuple _ -> true
    | Cosplit _ -> true
  ;;

  let is_coval (c : consumer) : bool =
    match c with
    | MuTilde _ -> false
    | Cotuple _ -> true
    | Split _ -> true
  ;;
end

module Eager : JUDGEMENTS = struct
  let name = "eager"

  let rec is_val (p : producer) : bool =
    let is_val_neutral n =
      match n with
      | Name (Free _) -> true
      | Name (Bound _) -> assert false
      | Negative _ -> true (* any consumer is a value. *)
      | Positive p -> is_val p
    in
    match p with
    | Mu _ -> false
    | Tuple xs -> List.fold_left (fun acc v -> acc && is_val_neutral v) true xs
    | Cosplit _ -> true
  ;;

  let rec is_coval (c : consumer) : bool =
    let is_coval_neutral n =
      match n with
      | Name (Free _) -> true
      | Name (Bound _) -> assert false
      | Positive _ -> true (* any producer is a covalue. *)
      | Negative c -> is_coval c
    in
    match c with
    | MuTilde _ -> false
    | Cotuple xs -> List.fold_left (fun acc v -> acc && is_coval_neutral v) true xs
    | Split _ -> true
  ;;
end

module Make_CBV (J : JUDGEMENTS) : EVALUATION_STRATEGY = struct
  type step =
    | Incomplete of cut
    | Complete of cut
    | Error of exn

  let name = Printf.sprintf "%s-call-by-value" J.name
  let is_val = J.is_val

  let producer_consumer_step p c =
    match p, c with
    (* encode type errors *)
    | Tuple _, Cotuple _ -> Error (Failure "type error: A*B producer, C&D consumer")
    | Tuple xs, Split (_, binders) when List.compare_lengths xs binders != 0 ->
      Error (Failure "type error: arity mismatch in tuple split")
    | Cosplit _, Split _ -> Error (Failure "type error: A&B producer, C*D consumer")
    | Cosplit (_, binders), Cotuple xs when List.compare_lengths xs binders != 0 ->
      Error (Failure "type error: arity mismatch in cotuple split")
    (* any letcc is immediately evaluated *)
    | Mu (cut, _), c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* any let is evaluated when the right is a covalue *)
    | p, MuTilde (cut, _) when is_val p ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* tuple semantics *)
    (* canonical tuple destruction *)
    | Tuple xs, Split (cut, _) when is_val (Tuple xs) ->
      (* beta-reduce each x in xs one by one *)
      List.fold_left
        (fun acc (x, i) ->
           Result.fold
             acc
             ~ok:(fun cut -> Beta_reducer.beta_reduce_with_neutral i x cut)
             ~error:(fun exn -> Error exn))
        (Ok cut)
        (List.mapi (fun i x -> x, i) xs)
      |> Result.fold ~ok:(fun cut -> Incomplete cut) ~error:(fun exn -> Error exn)
    (* tuple focusing rules, left to right *)
    | Tuple xs, cons ->
      (* find the element and position of the non-value in xs, create a continuation that feeds the non-value into that position *)
      let rec find_non_value lst index =
        match lst with
        | [] -> None
        | Name _ :: xs -> find_non_value xs (index + 1)
        | Negative _ :: xs -> find_non_value xs (index + 1)
        | Positive x :: xs ->
          if not (is_val x) then Some (x, index) else find_non_value xs (index + 1)
      in
      (match find_non_value xs 0 with
       | None -> Error (Failure "internal error: expected a non-value in tuple focusing")
       | Some (non_val, pos) ->
         let new_producer = Positive non_val in
         let new_consumer =
           (* map over the original list, but replace the non-value with a bound variable *)
           let new_elems =
             List.mapi (fun i x -> if i = pos then Name (Bound (0, None)) else x) xs
           in
           let tuple = Tuple new_elems in
           (* this is done in order to cut the non-value with a continuation, substituting that
           * non-value right there! (it will be evaluated at that point) *)
           Negative (MuTilde ({ p = Positive tuple; c = Negative cons }, None))
         in
         Incomplete { p = new_producer; c = new_consumer })
    (* any tuple below is already a value.
     * and since the only non_value was mu
     * and it has already been dealt with,
     * ANYTHING here is a value. *)
    (* catchall for any value and mutilde *)
    | p, MuTilde (cut, _) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* cotuple semantics - under CBV, the cotuple is not expected to focus.
     * cut any cotuple. *)
    | Cosplit (cut, _), Cotuple xs ->
      (* beta-reduce each x in xs one by one *)
      List.fold_left
        (fun acc (x, i) ->
           Result.fold
             acc
             ~ok:(fun cut -> Beta_reducer.beta_reduce_with_neutral i x cut)
             ~error:(fun exn -> Error exn))
        (Ok cut)
        (List.mapi (fun i x -> x, i) xs)
      |> Result.fold ~ok:(fun cut -> Incomplete cut) ~error:(fun exn -> Error exn)
  ;;

  let producer_name_step p n =
    let consumer = Name (Free n) in
    match p with
    | Mu (cut, _) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 consumer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | p when is_val p ->
      let cut = { p = Positive p; c = consumer } in
      Complete cut
    | Tuple xs ->
      (* find the element and position of the non-value in xs, create a continuation that feeds the non-value into that position *)
      let rec find_non_value lst index =
        match lst with
        | [] -> None
        | Name _ :: xs -> find_non_value xs (index + 1)
        | Negative _ :: xs -> find_non_value xs (index + 1)
        | Positive x :: xs ->
          if not (is_val x) then Some (x, index) else find_non_value xs (index + 1)
      in
      (match find_non_value xs 0 with
       | None -> Error (Failure "internal error: expected a non-value in tuple focusing")
       | Some (non_val, pos) ->
         let new_producer = Positive non_val in
         let new_consumer =
           (* map over the original list, but replace the non-value with a bound variable *)
           let new_elems =
             List.mapi (fun i x -> if i = pos then Name (Bound (0, None)) else x) xs
           in
           let tuple = Tuple new_elems in
           (* this is done in order to cut the non-value with a continuation, substituting that
           * non-value right there! (it will be evaluated at that point) *)
           Negative (MuTilde ({ p = Positive tuple; c = consumer }, None))
         in
         Incomplete { p = new_producer; c = new_consumer })
    | p ->
      let cut = { p = Positive p; c = consumer } in
      Complete cut
  ;;

  let name_consumer_step n c =
    let producer = Name (Free n) in
    match c with
    | MuTilde (cut, _) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 producer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
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
    | Tuple _, Cotuple _ -> Error (Failure "type error: A*B producer, C&D consumer")
    | Cosplit _, Split _ -> Error (Failure "type error: A&B producer, C*D consumer")
    (* any let is immediately evaluated *)
    | p, MuTilde (cut, _) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_producer 0 p cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* any letcc is evaluated when the right is a covalue *)
    | Mu (cut, _), c when is_coval c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* cotuple semantics *)
    (* canonical cotuple destruction *)
    | Cosplit (cut, _), Cotuple xs when is_coval (Cotuple xs) ->
      (* beta-reduce each x in xs one by one *)
      List.fold_left
        (fun acc (x, i) ->
           Result.fold
             acc
             ~ok:(fun cut -> Beta_reducer.beta_reduce_with_neutral i x cut)
             ~error:(fun exn -> Error exn))
        (Ok cut)
        (List.mapi (fun i x -> x, i) xs)
      |> Result.fold ~ok:(fun cut -> Incomplete cut) ~error:(fun exn -> Error exn)
    (* cotuple focusing rules, left to right *)
    | prod, Cotuple xs ->
      (* find the element and position of the non-covalue in xs, create a continuation that feeds the non-covalue into that position *)
      let rec find_non_covalue lst index =
        match lst with
        | [] -> None
        | Name _ :: xs -> find_non_covalue xs (index + 1)
        | Positive _ :: xs -> find_non_covalue xs (index + 1)
        | Negative x :: xs ->
          if not (is_coval x) then Some (x, index) else find_non_covalue xs (index + 1)
      in
      (match find_non_covalue xs 0 with
       | None ->
         Error (Failure "internal error: expected a non-covalue in cotuple focusing")
       | Some (non_coval, pos) ->
         let new_consumer = Negative non_coval in
         let new_producer =
           (* map over the original list, but replace the non-covalue with a bound variable *)
           let new_elems =
             List.mapi (fun i x -> if i = pos then Name (Bound (0, None)) else x) xs
           in
           let cotuple = Cotuple new_elems in
           (* this is done in order to cut the non-covalue with a continuation, substituting that
           * non-covalue right there! (it will be evaluated at that point) *)
           Positive (Mu ({ c = Negative cotuple; p = Positive prod }, None))
         in
         Incomplete { p = new_producer; c = new_consumer })
    (* any cotuple below is already a covalue.
     * and since the only non_covalue was mutilde
     * and it has already been dealt with,
     * ANYTHING here is a covalue. *)
    (* catchall for any covalue and mu *)
    | Mu (cut, _), c ->
      Result.fold
        (Beta_reducer.beta_reduce_with_consumer 0 c cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    (* tuple semantics - under CBN, the tuple is not expected to focus.
     * cut any tuple. *)
    (* tuple semantics - any potential simplification is only done
     * when the right side is completely simplified. in order to treat
     * the tuple using is_coval, we pretend it is a cotuple *)
    | Tuple xs, Split (cut, _) ->
      (* beta-reduce each x in xs one by one *)
      List.fold_left
        (fun acc (x, i) ->
           Result.fold
             acc
             ~ok:(fun cut -> Beta_reducer.beta_reduce_with_neutral i x cut)
             ~error:(fun exn -> Error exn))
        (Ok cut)
        (List.mapi (fun i x -> x, i) xs)
      |> Result.fold ~ok:(fun cut -> Incomplete cut) ~error:(fun exn -> Error exn)
  ;;

  let producer_name_step p n =
    let consumer = Name (Free n) in
    match p with
    | Mu (cut, _) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 consumer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | p ->
      let cut = { p = Positive p; c = consumer } in
      Complete cut
  ;;

  let name_consumer_step n c =
    let producer = Name (Free n) in
    match c with
    | MuTilde (cut, _) ->
      Result.fold
        (Beta_reducer.beta_reduce_with_neutral 0 producer cut)
        ~ok:(fun cut -> Incomplete cut)
        ~error:(fun exn -> Error exn)
    | c when is_coval c ->
      let cut = { p = producer; c = Negative c } in
      Complete cut
    | Cotuple xs ->
      (* find the element and position of the non-covalue in xs, create a continuation that feeds the non-covalue into that position *)
      let rec find_non_covalue lst index =
        match lst with
        | [] -> None
        | Name _ :: xs -> find_non_covalue xs (index + 1)
        | Positive _ :: xs -> find_non_covalue xs (index + 1)
        | Negative x :: xs ->
          if not (is_coval x) then Some (x, index) else find_non_covalue xs (index + 1)
      in
      (match find_non_covalue xs 0 with
       | None ->
         Error (Failure "internal error: expected a non-covalue in cotuple focusing")
       | Some (non_coval, pos) ->
         let new_consumer = Negative non_coval in
         let new_producer =
           (* map over the original list, but replace the non-covalue with a bound variable *)
           let new_elems =
             List.mapi (fun i x -> if i = pos then Name (Bound (0, None)) else x) xs
           in
           let cotuple = Cotuple new_elems in
           (* this is done in order to cut the non-covalue with a continuation, substituting that
           * non-covalue right there! (it will be evaluated at that point) *)
           Positive (Mu ({ c = Negative cotuple; p = producer }, None))
         in
         Incomplete { p = new_producer; c = new_consumer })
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
