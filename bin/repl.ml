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
    let new_r_pointer = (t.r_pointer + 1) mod t.size in
    if new_r_pointer = t.l_pointer then remove_one t;
    t.ring.(t.r_pointer) <- elem;
    Hashtbl.replace t.membership elem t.r_pointer;
    t.r_pointer <- new_r_pointer
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

let history = ref (History.init 1 "")
let print_result result = Printf.printf "=> %s\n%!" (Core.Show.show result)
let print_error msg = Printf.eprintf "Error: %s\n%!" msg
let get_ast str = str |> Reader.of_string ~filename:"REPL" |> Core.convert

let parse_and_eval (module Strategy : RUNNER) input =
  try
    let core_ast = get_ast input in
    let result = Strategy.eval core_ast in
    print_result result
  with
  | exn -> print_error (Printexc.to_string exn)
;;

let parse_and_step (module Strategy : RUNNER) input =
  print_endline "evaluating the module step by step...";
  print_endline "(any entry = step, :stop = exit)";
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
  history := History.init 1000 "";
  match LNoise.history_set ~max_length with
  | Error s -> raise (Failure s)
  | Ok () ->
    (* simple completion for REPL commands *)
    LNoise.set_completion_callback (fun line_so_far ln_completions ->
      if line_so_far = ""
      then ()
      else if line_so_far.[0] = ':'
      then [ ":q"; ":quit"; ":help" ] |> List.iter (LNoise.add_completion ln_completions)
      else
        !history
        |> History.filter (fun cmd ->
          String.length cmd >= String.length line_so_far
          && String.starts_with ~prefix:line_so_far cmd)
        |> List.iter (LNoise.add_completion ln_completions))
;;

let add_to_history line =
  ignore (LNoise.history_add line);
  History.add line !history
;;

let rec repl_loop strategy =
  let prompt = "moo> " in
  match LNoise.linenoise prompt with
  | None ->
    print_endline "\nGoodbye!";
    exit 0
  | Some "" -> repl_loop strategy
  | Some ":q" | Some ":quit" ->
    print_endline "Goodbye!";
    exit 0
  | Some ":help" ->
    print_endline "Commands:";
    print_endline "  :q, :quit    Exit REPL";
    print_endline "  :step <expr> Step-by-step evaluation";
    print_endline "  :help        Show this help";
    repl_loop strategy
  | Some line when String.starts_with ~prefix:":step " line ->
    add_to_history line;
    let expr = String.sub line 6 (String.length line - 6) |> String.trim in
    parse_and_step strategy expr;
    repl_loop strategy
  | Some line ->
    add_to_history line;
    parse_and_eval strategy line;
    repl_loop strategy
;;

let start_repl strategy_type =
  let strategy_name =
    match strategy_type with
    | `CBN -> "call-by-name"
    | `CBV -> "call-by-value"
  in
  Printf.printf "moo REPL (%s)\nType :q to quit\n%!" strategy_name;
  init_repl ();
  let strategy =
    match strategy_type with
    | `CBN -> (module Call_by_name : RUNNER)
    | `CBV -> (module Call_by_value : RUNNER)
  in
  try repl_loop strategy with
  | Sys.Break ->
    print_endline "Goodbye!";
    exit 0
;;
