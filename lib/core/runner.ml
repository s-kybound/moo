open Ir
open Utils.Fresh

(* generic runtime error *)
exception RuntimeError of string

(* Assertion error - something went horribly wrong *)
exception AssertionError of string
exception Exit of int64
exception Not_implemented

let force_term t : control_item list = [ T t; I Force ]

let extend_env (env : environment_frame) (new_bindings : (name * value) list)
  : environment_frame
  =
  List.fold_left
    (fun parent (binding, value) -> Frame { parent; binding; value })
    env
    new_bindings
;;

let lookup (env : environment_frame) (name : name) : value option =
  let rec aux current_env =
    match current_env with
    | Top -> None
    | Frame { parent; binding; value } ->
      if binding = name then Some value else aux parent
  in
  aux env
;;

let form_matches_value (form : form) (v : value) : bool =
  match form, v with
  | Binder _, _ -> true
  | Tuple form_names, VTuple v_list -> List.length form_names = List.length v_list
  | Constr { form_name; form_args }, VConstruction (cons_name, cons_args) ->
    form_name = cons_name && List.length form_args = List.length cons_args
  | Numeral n, VNum m -> n = m
  | _, _ -> false
;;

(* find the earliest match for a value. *)
let pattern_match (forms : (form * 'a) list) (value : value)
  : ((name * value) list * 'a) option
  =
  let rec aux forms =
    match forms with
    | [] -> None
    | (form, cmd) :: rest ->
      if form_matches_value form value
      then begin
        match form with
        | Binder name -> Some ([ name, value ], cmd)
        | Numeral _ -> Some ([], cmd)
        | Tuple names -> begin
          match value with
          | VTuple v_list ->
            let bindings = List.combine names v_list in
            Some (bindings, cmd)
          | _ -> None
        end
        | Constr { form_name = _; form_args = names } ->
        match value with
        | VConstruction (_cons_name, cons_args) ->
          let bindings = List.combine names cons_args in
          Some (bindings, cmd)
        | _ -> None
      end
      else aux rest
  in
  aux forms
;;

type channel = unit (* TODO *)

type program_step =
  | Step of state
  | Split of state * state
  | Stop
  | Error of exn
  | Send of value * channel * state
  | Receive of channel * (value -> state)

let eval_state (state : state) : program_step =
  match state with
  | [], _, _ -> raise (AssertionError "empty control stack")
  | T term :: c', s, e -> begin
    match term with
    | NeedsForce t -> Step (force_term t @ c', s, e)
    | Mu (name, cmd) -> Step (c', VMu (name, [ C cmd ], [], e) :: s, e)
    | Variable name -> begin
      match lookup e name with
      | Some v -> Step (c', v :: s, e)
      | None -> raise (AssertionError ("unbound variable: " ^ name))
    end
    | Construction { cons_name; cons_args } ->
      let arg_eval_sequcence =
        List.map (fun arg -> T arg) cons_args
        @ [ I (Con_instr (cons_name, List.length cons_args)) ]
      in
      Step (arg_eval_sequcence @ c', s, e)
    | Tuple terms ->
      let term_eval_sequence =
        List.map (fun t -> T t) terms @ [ I (Tup_instr (List.length terms)) ]
      in
      Step (term_eval_sequence @ c', s, e)
    | Matcher patterns_cmds -> Step (c', VMatcher (patterns_cmds, e) :: s, e)
    | Num n -> Step (c', VNum n :: s, e)
    | Rec (_name, _t) -> raise Not_implemented
    | Arr terms ->
      let term_eval_sequence =
        List.map (fun t -> T t) terms @ [ I (Arr_instr (List.length terms)) ]
      in
      Step (term_eval_sequence @ c', s, e)
    | Exit -> Step (c', VExit :: s, e)
  end
  (* instructions *)
  | I Force :: c', VMu (name, mu_c, mu_s, mu_e) :: s', e ->
    let k_name = genvar "k" in
    let captured_mu = VMu (k_name, c', s', e) in
    let new_e = extend_env mu_e [ name, captured_mu ] in
    Step (mu_c, mu_s, new_e)
  | I Force :: c', v :: s', e ->
    (* non-thunk value, force has no effect *)
    Step (c', v :: s', e)
  | I Cut :: _c', unfocus_val :: focus_val :: _s', _e ->
    (match focus_val, unfocus_val with
     (* "active" computation binding *)
     | VMu _, _ -> raise (AssertionError "focused value cannot be a mu thunk")
     | _, VMu (name, mu_c, mu_s, mu_e) ->
       let new_e = extend_env mu_e [ name, focus_val ] in
       Step (mu_c, mu_s, new_e)
     (* invalid states - self matching
      * these should have been handled in the typechecking *)
     | VExit, VExit -> raise (AssertionError " two exit values")
     | VArr _, VArr _ -> raise (AssertionError "cannot cut two array values")
     | VTuple _, VTuple _ -> raise (AssertionError "cannot cut two tuple values")
     | VConstruction _, VConstruction _ ->
       raise (AssertionError "cannot cut two construction values")
     | VNum _, VNum _ -> raise (AssertionError "cannot cut two numeric values")
     | VMatcher _, VMatcher _ -> raise (AssertionError "cannot cut two matcher values")
     (* exit semantics *)
     | VExit, VNum n | VNum n, VExit -> Error (Exit n)
     (* array semantics -- TODO *)
     (* match semantics *)
     | VMatcher (cases, match_e), adt | adt, VMatcher (cases, match_e) ->
       (match pattern_match cases adt with
        | Some (bindings, cmd) ->
          let new_e = extend_env match_e bindings in
          Step ([ C cmd ], [], new_e)
        (* failure to pattern match should not happen *)
        | None -> raise (AssertionError "no matching pattern found"))
     (* invalid states - attempt to match value to non-mu value *)
     | VExit, x | x, VExit ->
       let exit_msg =
         Printf.sprintf
           "attempt to cut exit value with non-exit value: %s"
           (Pretty.show_value x)
       in
       raise (AssertionError exit_msg)
     | VArr _, _ -> raise (AssertionError "attempt to cut array value with value")
     | VTuple _, _ -> raise (AssertionError "attempt to cut tuple value with value")
     | VConstruction _, _ ->
       raise (AssertionError "attempt to cut construction value with value")
     | VNum _, _ -> raise (AssertionError "attempt to cut numeric value with value"))
  | I (Spawn cmd2) :: c', s', e' ->
    (* TODO: check whether this is the correct formulation - should s' be preserved in one or the other or etc? *)
    let state1 = c', s', e' in
    let state2 = [ C cmd2 ], [], e' in
    Split (state1, state2)
  | I (Unop_instr op) :: c', v :: s', e ->
    (match op, v with
     | Neg, VNum n ->
       let result = Int64.neg n in
       Step (c', VNum result :: s', e)
     | Not, VNum n ->
       let result = Int64.lognot n in
       Step (c', VNum result :: s', e)
     | _ -> raise (AssertionError "unop applied to invalid value"))
  | I (Bop_instr op) :: c', v2 :: v1 :: s', e ->
    let safe_operate f n1 n2 k =
      try
        let result = f n1 n2 in
        Step (c', VNum result :: s', e)
      with
      | Division_by_zero -> raise (RuntimeError "division by zero")
      | _ -> raise (AssertionError ("invalid binary operation: " ^ k))
    in
    (match op, v1, v2 with
     | Add, VNum n1, VNum n2 -> safe_operate Int64.add n1 n2 "addition"
     | Sub, VNum n1, VNum n2 -> safe_operate Int64.sub n1 n2 "subtraction"
     | Mul, VNum n1, VNum n2 -> safe_operate Int64.mul n1 n2 "multiplication"
     | Div, VNum n1, VNum n2 -> safe_operate Int64.div n1 n2 "division"
     | Mod, VNum n1, VNum n2 -> safe_operate Int64.rem n1 n2 "modulus"
     | And, VNum n1, VNum n2 -> safe_operate Int64.logand n1 n2 "bitwise and"
     | Or, VNum n1, VNum n2 -> safe_operate Int64.logor n1 n2 "bitwise or"
     | Xor, VNum n1, VNum n2 -> safe_operate Int64.logxor n1 n2 "bitwise xor"
     | Shl, VNum n1, VNum n2 ->
       let shift_amount = Int64.to_int n2 in
       if shift_amount < 0
       then raise (RuntimeError "negative shift amount")
       else (
         let result = Int64.shift_left n1 shift_amount in
         Step (c', VNum result :: s', e))
     | Shr, VNum n1, VNum n2 ->
       let shift_amount = Int64.to_int n2 in
       if shift_amount < 0
       then raise (RuntimeError "negative shift amount")
       else (
         let result = Int64.shift_right n1 shift_amount in
         Step (c', VNum result :: s', e))
     | _ -> raise (AssertionError "bop applied to invalid values"))
  | I (Con_instr (name, arity)) :: c', s, e when List.length s >= arity ->
    let args = List.rev (List.take arity s) in
    let s' = List.drop arity s in
    Step (c', VConstruction (name, args) :: s', e)
  | I (Tup_instr arity) :: c', s, e when List.length s >= arity ->
    let args = List.rev (List.take arity s) in
    let s' = List.drop arity s in
    Step (c', VTuple args :: s', e)
  | I (Arr_instr arity) :: c', s, e when List.length s >= arity ->
    let args = List.rev (List.take arity s) in
    let s' = List.drop arity s in
    Step (c', VArr (Array.of_list args) :: s', e)
  (* invalid instruction states *)
  | I Force :: _, [], _ -> raise (AssertionError "stack underflow on force")
  | I Cut :: _, _, _ -> raise (AssertionError "stack underflow on cut")
  | I (Unop_instr _) :: _, _, _ -> raise (AssertionError "stack underflow on unop")
  | I (Bop_instr _) :: _, _, _ -> raise (AssertionError "stack underflow on bop")
  | I (Con_instr _) :: _, _, _ -> raise (AssertionError "stack underflow on constructor")
  | I (Tup_instr _) :: _, _, _ -> raise (AssertionError "stack underflow on tuple")
  | I (Arr_instr _) :: _, _, _ -> raise (AssertionError "stack underflow on array")
  (* commands *)
  | C cmd :: c', s, e ->
  match cmd with
  | ModEndHole -> Stop
  | Fork (cmd1, cmd2) -> Step (I (Spawn cmd2) :: C cmd1 :: c', s, e)
  | Core { focus_term; unfocus_term } ->
    Step (force_term focus_term @ (T unfocus_term :: I Cut :: c'), s, e)
  | Arith (Unop { op; in_focus_term; out_unfocus_term }) ->
    Step
      ( force_term in_focus_term @ (I (Unop_instr op) :: T out_unfocus_term :: I Cut :: c')
      , s
      , e )
  | Arith (Bop { op; l_focus_term; r_focus_term; out_unfocus_term }) ->
    Step
      ( force_term l_focus_term
        @ force_term r_focus_term
        @ (I (Bop_instr op) :: T out_unfocus_term :: I Cut :: c')
      , s
      , e )
;;

let state_of_command (cmd : command) : state = [ C cmd ], [], Ir.empty_environment

let eval_program (initial_state : state) : int64 * environment_frame =
  let work_queue : program_step Queue.t = Queue.create () in
  Queue.add (Step initial_state) work_queue;
  let rec runner status curr_frame immediate =
    let next_item =
      match immediate with
      | Some item -> Some item
      | None -> if Queue.is_empty work_queue then None else Some (Queue.take work_queue)
    in
    match next_item with
    | None -> status, curr_frame
    | Some (Step state) ->
      let next_step = eval_state state in
      Queue.add next_step work_queue;
      runner status curr_frame None
    | Some Stop -> runner status curr_frame None
    | Some (Split (state1, state2)) ->
      Queue.add (Step state2) work_queue;
      runner status curr_frame (Some (Step state1))
    | Some (Send (_v, _chan, _next)) -> raise Not_implemented
    | Some (Receive (_chan, _cont)) -> raise Not_implemented
    | Some (Error exn) -> raise exn (* TODO: better error handling *)
  in
  runner Int64.zero Ir.empty_environment None
;;
