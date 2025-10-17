open Moo
open Ast
open Runner
open Typechecker

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
  let current_evaluator : (module EVALUATION_STRATEGY) option ref = ref None
  let current_typechecker : (module TYPECHECKER) option ref = ref None
  let current_val_strat : [ `Lazy | `Eager ] ref = ref `Eager
  let current_eval_strat : [ `CBN | `CBV ] ref = ref `CBV

  let current_typecheck_strat
    : [ `Untyped | `Simply_typed | `System_f | `Hindley_milner ] ref
    =
    ref `Untyped
  ;;

  let current_environment : Env.t ref = ref (Env.empty_env ())

  let set_evaluator eval_strat val_strat typecheck_strat =
    current_eval_strat := eval_strat;
    current_val_strat := val_strat;
    current_typecheck_strat := typecheck_strat;
    let (module Typechecker : TYPECHECKER) =
      match typecheck_strat with
      | `Untyped -> (module Typechecker.Untyped)
      | `Simply_typed -> (module Typechecker.SimplyTyped)
      | `System_f -> (module Typechecker.SystemF)
      | `Hindley_milner -> (module Typechecker.HindleyMilner)
    in
    current_typechecker := Some (module Typechecker);
    let (module J : JUDGEMENTS) =
      match val_strat with
      | `Lazy -> (module Lazy)
      | `Eager -> (module Eager)
    in
    let t : (module EVALUATION_STRATEGY) =
      match eval_strat with
      | `CBN -> (module Make_CBN (J))
      | `CBV -> (module Make_CBV (J))
    in
    current_evaluator := Some t
  ;;

  let set_history t = current_history := Some t
  let clear_environment () = current_environment := Env.empty_env ()

  let get_evaluator () =
    match !current_evaluator with
    | None -> raise (Failure "Tried to get uninitialized evaluator")
    | Some e -> e
  ;;

  let get_typechecker () =
    match !current_typechecker with
    | None -> raise (Failure "Tried to get uninitialized typechecker")
    | Some e -> e
  ;;

  let get_history () =
    match !current_history with
    | None -> raise (Failure "Tried to get uninitialized history")
    | Some e -> e
  ;;
end

let print_ast ast = Printf.printf "%s\n%!" (Core.Show.show ast)
let print_result result = Printf.printf "=> %s\n%!" (Core.Show.show_cut result)
let print_error msg = Printf.eprintf "Error: %s\n%!" msg
let get_ast str = str |> Reader.of_string ~filename:"REPL" |> Core.convert

let parse_and_eval input =
  let (module Strategy : EVALUATION_STRATEGY) = State.get_evaluator () in
  let (module Typechecker : TYPECHECKER) = State.get_typechecker () in
  try
    let core_ast = get_ast input in
    match Typechecker.typecheck core_ast with
    | Error exn -> raise exn
    | Ok core_ast ->
      let result = Strategy.eval !State.current_environment core_ast in
      print_result result
  with
  | exn -> print_error (Printexc.to_string exn)
;;

let parse_and_show input =
  try
    let core_ast = get_ast input in
    print_ast core_ast
  with
  | exn -> print_error (Printexc.to_string exn)
;;

let parse_and_step input =
  print_endline "evaluating the module step by step...";
  print_endline "(any entry = step, :stop = exit)";
  let (module Strategy : EVALUATION_STRATEGY) = State.get_evaluator () in
  let rec step_eval cut =
    Printf.printf "current result: %s\n%!" (Core.Show.show_cut cut);
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
    Env.load_definitions core_ast !State.current_environment;
    let new_main = Env.substitute_definitions core_ast.main !State.current_environment in
    step_eval new_main
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
      then
        [ ":q"
        ; ":quit"
        ; ":exit"
        ; ":help"
        ; ":step"
        ; ":show"
        ; ":cbn"
        ; ":call-by-name"
        ; ":cbv"
        ; ":call-by-value"
        ; ":eager"
        ; ":lazy"
        ; ":clear"
        ; ":load"
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

let load_file filename =
  try
    let ast = Reader.of_file filename in
    let converted = Core.convert ast in
    Env.load_definitions converted !State.current_environment;
    Printf.printf "Loaded definitions from %s\n%!" filename
  with
  | Sys_error msg -> print_error ("File error: " ^ msg)
  | exn -> print_error ("Parse error in " ^ filename ^ ": " ^ Printexc.to_string exn)
;;

let multiline_prompt base_prompt =
  let base_prompt_length = String.length base_prompt in
  let multiline_prompt length = String.make (length - 5) ' ' ^ "...> " in
  let rec aux acc =
    let prompt =
      match acc with
      | [] -> base_prompt
      | _ -> multiline_prompt base_prompt_length
    in
    match LNoise.linenoise prompt with
    | None -> None
    | Some line when String.ends_with ~suffix:"\\" (String.trim line) -> aux (line :: acc)
    | Some line -> line :: acc |> List.rev |> String.concat "" |> Option.some
  in
  aux [] |> Option.map String.trim
;;

let rec repl_loop () =
  let (module Strategy : EVALUATION_STRATEGY) = State.get_evaluator () in
  let prompt = Printf.sprintf "moo[%s]> " Strategy.name in
  match multiline_prompt prompt with
  | None ->
    print_endline "\nGoodbye!";
    exit 0
  | Some "" -> repl_loop ()
  | Some ":q" | Some ":quit" | Some ":exit" ->
    print_endline "Goodbye!";
    exit 0
  | Some ":cbn" | Some ":call-by-name" ->
    State.set_evaluator `CBN !State.current_val_strat !State.current_typecheck_strat;
    repl_loop ()
  | Some ":cbv" | Some ":call-by-value" ->
    State.set_evaluator `CBV !State.current_val_strat !State.current_typecheck_strat;
    repl_loop ()
  | Some ":lazy" ->
    State.set_evaluator !State.current_eval_strat `Lazy !State.current_typecheck_strat;
    repl_loop ()
  | Some ":eager" ->
    State.set_evaluator !State.current_eval_strat `Eager !State.current_typecheck_strat;
    repl_loop ()
  | Some ":clear" ->
    State.clear_environment ();
    repl_loop ()
  | Some ":help" ->
    print_endline "Commands:";
    print_endline "  :q, :quit, :exit      Exit REPL";
    print_endline "  :cbn, :call-by-name   Switch to call-by-name evaluation";
    print_endline "  :cbv, :call-by-value  Switch to call-by-value evaluation";
    print_endline "  :lazy                 Switch to lazy evaluation";
    print_endline "  :eager                Switch to eager evaluation";
    print_endline "  :clear                Clear the REPL environment";
    print_endline "  :show <expr>          Visualize the expression";
    print_endline "  :step <expr>          Step-by-step evaluation";
    print_endline "  :load <filename>      Load all definitions from a file into the REPL";
    print_endline "  :help                 Show this help";
    repl_loop ()
  | Some line when String.starts_with ~prefix:":step " line ->
    add_to_history line;
    let expr = String.sub line 6 (String.length line - 6) |> String.trim in
    parse_and_step expr;
    repl_loop ()
  | Some line when String.starts_with ~prefix:":show " line ->
    add_to_history line;
    let expr = String.sub line 6 (String.length line - 6) |> String.trim in
    parse_and_show expr;
    repl_loop ()
  | Some line when String.starts_with ~prefix:":load " line ->
    add_to_history line;
    let filename = String.sub line 6 (String.length line - 6) |> String.trim in
    if filename = "" then print_error "Usage: :load <filename>" else load_file filename;
    repl_loop ()
  | Some line ->
    add_to_history line;
    parse_and_eval line;
    repl_loop ()
;;

let start_repl eval_strat value_strat typecheck_strat =
  init_repl ();
  State.set_evaluator eval_strat value_strat typecheck_strat;
  let (module Strategy) = State.get_evaluator () in
  Printf.printf
    "Welcome to moo %s.\nType \":help\" for more information.\n%!"
    Utils.version;
  try repl_loop () with
  | Sys.Break ->
    print_endline "Goodbye!";
    exit 0
;;
