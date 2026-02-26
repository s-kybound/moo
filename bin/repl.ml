open Syntax
open Moo

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
  let set_history t = current_history := Some t

  let get_history () =
    match !current_history with
    | None -> raise (Failure "Tried to get uninitialized history")
    | Some e -> e
  ;;
end

let print_ast ast = Printf.printf "%s\n%!" (Pretty.show_program ast)
let print_error msg = Printf.eprintf "Error: %s\n%!" msg

let print_exception_with_context source exn =
  match exn with
  | Error.Syntax_error { span = Some span; message } ->
    let snippet = Utils.display_span source span in
    Printf.eprintf "%s\nSyntax Error: %s\n%!" snippet message
  | Error.Syntax_error { span = None; message } ->
    Printf.eprintf "Syntax Error: %s\n%!" message
  | Typechecker.Bidir.TypeError { loc = Some loc; message } ->
    let snippet = Utils.display_span source loc in
    Printf.eprintf "%s\nType Error: %s\n%!" snippet message
  | Typechecker.Bidir.TypeError { loc = None; message } ->
    Printf.eprintf "Type Error: %s\n%!" message
  | _ -> print_error (Printexc.to_string exn)
;;

let parse_to_core_ast ?k input =
  input
  |> Reader.of_string ?k ~filename:"REPL"
  |> Surface_to_ast.surface_module_to_ast_module
;;

let eval_module input =
  let tychecked, _ = Typechecker.Bidir.tycheck_program input in
  let converted = Core.Tycheck_to_ir.tycheck_command_of_module tychecked in
  let converted = Core.Runner.state_of_command converted in
  ignore (Core.Runner.eval_program converted)
;;

let step_module input =
  let show_state (control, stash, _env) =
    Printf.printf "Control Stack:\n";
    List.iter
      (fun ci -> Printf.printf "  %s\n" (Core.Pretty.show_control_item ci))
      control;
    Printf.printf "Stash:\n";
    List.iter (fun v -> Printf.printf "  %s\n" (Core.Pretty.show_value v)) stash;
    Printf.printf "\n%!"
  in
  let rec step_loop states =
    let open Core.Runner in
    match states with
    | [] -> Printf.printf "No more states to step through.\n%!"
    | Step state :: rest ->
      show_state state;
      begin match LNoise.linenoise "STEP> " with
      | None -> ()
      | Some s ->
      match String.trim s with
      | "\\q" | "\\quit" | "\\exit" -> ()
      | _ ->
        let next_state = eval_state state in
        step_loop (rest @ [ next_state ])
      end
    | Stop :: rest -> step_loop rest
    | Split (state1, state2) :: rest ->
      Printf.printf "Program split into two concurrent states.\n%!";
      step_loop ((Step state1 :: rest) @ [ Step state2 ])
    | Send (_v, _chan, _next) :: _rest ->
      print_error "Step-through for Send not implemented."
    | Receive (_chan, _cont) :: _rest ->
      print_error "Step-through for Receive not implemented."
    | Error exn :: _ -> print_error (Printexc.to_string exn)
  in
  let tychecked, _ = Typechecker.Bidir.tycheck_program input in
  let converted = Core.Tycheck_to_ir.tycheck_command_of_module tychecked in
  let converted = Core.Runner.state_of_command converted in
  Printf.printf
    "Stepping through program. Press any key to step through the program, \\q to quit\n%!";
  step_loop [ Step converted ]
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
        [ ":q"; ":quit"; ":exit"; ":help"; ":step"; ":show"; ":clear"; ":load" ]
        |> List.iter (LNoise.add_completion ln_completions)
      else
        State.get_history ()
        |> History.filter (fun cmd ->
          String.length cmd >= String.length line_so_far
          && String.starts_with ~prefix:line_so_far cmd)
        |> List.iter (LNoise.add_completion ln_completions))
;;

let add_to_history line =
  let trim_input =
    line |> String.split_on_char '\n' |> List.map String.trim |> String.concat " "
  in
  ignore (LNoise.history_add trim_input);
  History.add trim_input (State.get_history ())
;;

(* If there is some context waiting (a checkpoint), we resume parsing from that point *)
let rec repl_loop (kont : (Error.kont * (Ast.core_ann Ast.module_ -> 'a) * string) option)
  =
  let attempt_eval ?(previous_input = "") ?k input f =
    let full_input =
      if String.trim previous_input = "" then input else previous_input ^ "\n" ^ input
    in
    try f (parse_to_core_ast ?k input) with
    | Error.Early_eof k -> repl_loop (Some (k, f, full_input))
    | e ->
      print_exception_with_context full_input e;
      repl_loop None
  in
  let prompt =
    match kont with
    | Some _ -> "... "
    | None -> ">>> "
  in
  match LNoise.linenoise prompt with
  | None ->
    print_endline "\nGoodbye!";
    exit 0
  | Some line ->
    add_to_history line;
    (match String.trim line, kont with
     | "", None -> repl_loop kont
     | "", Some (k, f, previous_input) ->
       (* we need to consider the newlines here for correctness *)
       attempt_eval ~previous_input ~k line f;
       repl_loop None
     | "\\q", _ | "\\quit", _ | "\\exit", _ ->
       print_endline "Goodbye!";
       exit 0
     | "\\help", _ ->
       print_endline "Commands:";
       print_endline "  \\q, \\quit, \\exit   Exit REPL";
       print_endline "  \\show <program>      Visualize the expression";
       print_endline "  \\help                Show this help";
       print_endline "  \\step <program>      Step through the program (not implemented)";
       repl_loop kont
     | l, None when String.starts_with ~prefix:"\\step " l ->
       let expr = String.sub l 6 (String.length l - 6) in
       attempt_eval expr step_module;
       repl_loop None
     | l, None when String.starts_with ~prefix:"\\show " l ->
       let expr = String.sub l 6 (String.length l - 6) in
       attempt_eval expr print_ast;
       repl_loop None
     | _, Some (k, f, previous_input) ->
       attempt_eval ~previous_input ~k line f;
       repl_loop None
     | _, None ->
       attempt_eval line eval_module;
       repl_loop None)
;;

let start_repl () =
  init_repl ();
  Printf.printf
    "Welcome to moo %s.\nType \"\\help\" for more information.\n%!"
    Version.version;
  try repl_loop None with
  | Sys.Break ->
    print_endline "Goodbye!";
    exit 0
;;
