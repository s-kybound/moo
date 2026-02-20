open Syntax
open Lexing

let with_filename buffer name =
  buffer.lex_curr_p <- { buffer.lex_curr_p with pos_fname = name };
  buffer
;;

let with_position buffer (position : position) =
  (* make a position starting from the next line *)
  buffer.lex_start_p <- position;
  buffer.lex_curr_p <- position;
  buffer
;;

let parse = Incremental.parse_module
let resume_parse = Incremental.resume_parse_module

let of_channel ~filename ic =
  let lb = with_filename (Lexing.from_channel ic) filename in
  parse lb
;;

let of_string ?(k : Error.kont option) ?(filename = "<string>") s =
  match k with
  | None ->
    let lb = with_filename (Lexing.from_string s) filename in
    parse lb
  | Some (k, resume_pos) ->
    let resumed = "\n" ^ s in
    let lb = with_filename (Lexing.from_string resumed) filename in
    resume_parse (with_position lb resume_pos) k
;;

let of_file filename =
  let ic = open_in filename in
  Fun.protect ~finally:(fun () -> close_in_noerr ic) (fun () -> of_channel ~filename ic)
;;
