open Moo
open Ast
open Runner

(* O(1) addition, O(1) (implicit) deletion,
 * allows us to filter and access the relevant
 * list of items in O(n) *)
module History = struct
  type 'a t =
    { ring : 'a array
    ; size : int
    ; mutable l_pointer : int
    ; mutable r_pointer : int
    ; membership : ('a, int) Hashtbl.t
    }

  let init size empty =
    assert (size > 0);
    let membership = Hashtbl.create size in
    let ring = Array.make size empty in
    { ring; size; l_pointer = 0; r_pointer = 0; membership }
  ;;

  let remove_one t =
    let elem_to_remove = t.ring.(t.l_pointer) in
    Hashtbl.remove t.membership elem_to_remove;
    let new_l_pointer = (t.l_pointer + 1) mod t.size in
    t.l_pointer <- new_l_pointer
  ;;

  let add elem t =
    if Hashtbl.mem t.membership elem
    then ()
    else (
      let new_r_pointer = (t.r_pointer + 1) mod t.size in
      if new_r_pointer = t.l_pointer then remove_one t;
      t.ring.(t.r_pointer) <- elem;
      Hashtbl.replace t.membership elem t.r_pointer;
      t.r_pointer <- new_r_pointer)
  ;;

  let get_stack t =
    (* only get the items from l_pointer to r_pointer (stack treatment) *)
    let rec aux acc i =
      if i = t.r_pointer
      then acc
      else (
        let elem = t.ring.(i) in
        let next_i = (i + 1) mod t.size in
        aux (elem :: acc) next_i)
    in
    if t.l_pointer = t.r_pointer then [] else aux [] t.l_pointer
  ;;

  let filter f t = t |> get_stack |> List.filter f
end

module State = struct
  let current_history : string History.t option ref = ref None
  let current_evaluator : (module RUNNER) option ref = ref None
  let set_evaluator t = current_evaluator := Some t
  let set_history t = current_history := Some t

  let get_evaluator () =
    match !current_evaluator with
    | None -> raise (Failure "Tried to get uninitialized evaluator")
    | Some e -> e
  ;;

  let get_history () =
    match !current_history with
    | None -> raise (Failure "Tried to get uninitialized history")
    | Some e -> e
  ;;
end

let print_result result = Printf.printf "=> %s\n%!" (Core.Show.show result)
let print_error msg = Printf.eprintf "Error: %s\n%!" msg
let get_ast str = str |> Reader.of_string ~filename:"REPL" |> Core.convert

let parse_and_eval input =
  let (module Strategy : RUNNER) = State.get_evaluator () in
  try
    let core_ast = get_ast input in
    let result = Strategy.eval core_ast in
    print_result result
  with
  | exn -> print_error (Printexc.to_string exn)
;;

let parse_and_step input =
  print_endline "evaluating the module step by step...";
  print_endline "(any entry = step, :stop = exit)";
  let (module Strategy : RUNNER) = State.get_evaluator () in
  let rec step_eval cut =
    Printf.printf "current result: %s\n%!" (Core.Show.show cut);
    match LNoise.linenoise "step> " with
    | None | Some ":exit" -> print_endline "exiting"
    | Some _ ->
      Printf.printf "Stepping...\n%!";
      (match Strategy.step_once cut with
       | Strategy.Complete result ->
         Printf.printf "Complete!\n%!";
         print_result result
       | Strategy.Incomplete next_cut -> step_eval next_cut
       | Strategy.Error exn -> raise exn)
  in
  try
    let core_ast = get_ast input in
    step_eval core_ast
  with
  | exn -> print_error (Printexc.to_string exn)
;;

let init_repl () =
  LNoise.set_multiline true;
  let max_length = 1000 in
  State.set_history (History.init 1000 "");
  match LNoise.history_set ~max_length with
  | Error s -> raise (Failure s)
  | Ok () ->
    (* simple completion for REPL commands *)
    LNoise.set_completion_callback (fun line_so_far ln_completions ->
      if line_so_far = ""
      then ()
      else if line_so_far.[0] = ':'
      then
        [ ":q"
        ; ":quit"
        ; ":exit"
        ; ":help"
        ; ":step"
        ; ":cbn"
        ; ":call-by-name"
        ; ":cbv"
        ; ":call-by-value"
        ]
        |> List.iter (LNoise.add_completion ln_completions)
      else
        State.get_history ()
        |> History.filter (fun cmd ->
          String.length cmd >= String.length line_so_far
          && String.starts_with ~prefix:line_so_far cmd)
        |> List.iter (LNoise.add_completion ln_completions))
;;

let add_to_history line =
  ignore (LNoise.history_add line);
  History.add line (State.get_history ())
;;

let rec repl_loop () =
  let (module Strategy : RUNNER) = State.get_evaluator () in
  let prompt = Printf.sprintf "moo[%s]> " Strategy.name in
  match LNoise.linenoise prompt with
  | None ->
    print_endline "\nGoodbye!";
    exit 0
  | Some "" -> repl_loop ()
  | Some ":q" | Some ":quit" | Some ":exit" ->
    print_endline "Goodbye!";
    exit 0
  | Some ":cbn" | Some ":call-by-name" ->
    State.set_evaluator (module Call_by_name);
    repl_loop ()
  | Some ":cbv" | Some ":call-by-value" ->
    State.set_evaluator (module Call_by_value);
    repl_loop ()
  | Some ":help" ->
    print_endline "Commands:";
    print_endline "  :q, :quit, :exit   Exit REPL";
    print_endline "  :cbn, :call-by-name   Switch to call-by-name evaluation";
    print_endline "  :cbv, :call-by-value  Switch to call-by-value evaluation";
    print_endline "  :step <expr>       Step-by-step evaluation";
    print_endline "  :help              Show this help";
    repl_loop ()
  | Some line when String.starts_with ~prefix:":step " line ->
    add_to_history line;
    let expr = String.sub line 6 (String.length line - 6) |> String.trim in
    parse_and_step expr;
    repl_loop ()
  | Some line ->
    add_to_history line;
    parse_and_eval line;
    repl_loop ()
;;

let start_repl strategy_type =
  init_repl ();
  let (module Strategy) =
    match strategy_type with
    | `CBN -> (module Call_by_name : RUNNER)
    | `CBV -> (module Call_by_value : RUNNER)
  in
  State.set_evaluator (module Strategy);
  Printf.printf "moo REPL (%s) - enter :q to quit\n%!" Strategy.name;
  try repl_loop () with
  | Sys.Break ->
    print_endline "Goodbye!";
    exit 0
;;
