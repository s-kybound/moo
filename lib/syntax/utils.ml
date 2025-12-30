open Loc
open Error

let get_lexing_position lexbuf : position =
  let pos = Lexing.lexeme_start_p lexbuf in
  let file = if pos.Lexing.pos_fname = "" then None else Some pos.Lexing.pos_fname in
  { file; line = pos.Lexing.pos_lnum; col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 }
;;

let display_position source_code position =
  let lines = String.split_on_char '\n' source_code in
  let line_num = position.line - 1 in
  if line_num < 0 || line_num >= List.length lines
  then "Position out of bounds"
  else (
    let line = List.nth lines line_num in
    let line_indicator = Printf.sprintf "%d | " position.line in
    let line_with_number = line_indicator ^ line in
    let pointer_line =
      String.make (position.col + (String.length line_indicator - 1)) ' ' ^ "^"
    in
    Printf.sprintf "%s\n%s" line_with_number pointer_line)
;;

let display_syntax_error source_code err =
  match err with
  | Syntax_error { position = None; message } -> Printf.sprintf "Syntax Error: %s" message
  | Syntax_error { position = Some pos; message } ->
    let code_snippet = display_position source_code pos in
    Printf.sprintf
      "%sLine %d, Column %d:\n%s\nSyntax Error: %s"
      (match pos.file with
       | Some fname -> Printf.sprintf "File \"%s\", " fname
       | None -> "")
      pos.line
      pos.col
      code_snippet
      message
  | _ -> "Unknown error"
;;
