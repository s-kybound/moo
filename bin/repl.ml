open Moo
open Ast
open Runner

let print_prompt () =
  print_string "moo> ";
  flush stdout
;;

let print_result result = Printf.printf "=> %s\n" (Core.Show.show result)
let print_error msg = Printf.eprintf "Error: %s\n" msg
let get_ast str = str |> Reader.of_string ~filename:"REPL" |> Core.convert

let parse_and_eval (module Strategy : RUNNER) input =
  try
    let core_ast = get_ast input in
    let result = Strategy.eval core_ast in
    print_result result
  with
  | exn -> print_error (Printexc.to_string exn)
;;

let rec repl_loop strategy =
  print_prompt ();
  match In_channel.input_line stdin with
  | None -> print_endline "\nGoodbye!"
  | Some "" -> repl_loop strategy
  | Some ":q" -> print_endline "Goodbye!"
  | Some line ->
    parse_and_eval strategy line;
    repl_loop strategy
;;

let start_repl strategy_type =
  let strategy =
    match strategy_type with
    | `CBN -> (module Call_by_name : RUNNER)
    | `CBV -> (module Call_by_value : RUNNER)
  in
  let strategy_name =
    match strategy_type with
    | `CBN -> "call-by-name"
    | `CBV -> "call-by-value"
  in
  Printf.printf "moo REPL (%s)\nType :q to quit\n" strategy_name;
  try repl_loop strategy with
  | End_of_file -> print_endline "\nGoodbye!"
;;
