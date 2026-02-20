open Loc

let position_of_lexing_pos (pos : Lexing.position) : position =
  let file = if pos.Lexing.pos_fname = "" then None else Some pos.Lexing.pos_fname in
  { file; line = pos.Lexing.pos_lnum; col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 }
;;

let get_lexing_position lexbuf : position =
  let pos = Lexing.lexeme_start_p lexbuf in
  position_of_lexing_pos pos
;;

let get_lexing_span lexbuf : span =
  let start_pos = position_of_lexing_pos (Lexing.lexeme_start_p lexbuf) in
  let end_pos = position_of_lexing_pos (Lexing.lexeme_end_p lexbuf) in
  { start_pos; end_pos }
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

let display_multiline_span source_code (span : span) =
  let lines = String.split_on_char '\n' source_code in
  let line_count = List.length lines in
  let start_line = max 1 (span.start_pos.line - 1) in
  let end_line = min line_count (span.end_pos.line + 1) in
  let pointer_line line_number line_text =
    let line_indicator = Printf.sprintf "%d | " line_number in
    let start_col, end_col =
      if span.start_pos.line = span.end_pos.line
      then span.start_pos.col, max span.start_pos.col (span.end_pos.col - 1)
      else if line_number = span.start_pos.line
      then span.start_pos.col, max span.start_pos.col (String.length line_text)
      else if line_number = span.end_pos.line
      then 1, max 1 (span.end_pos.col - 1)
      else 1, max 1 (String.length line_text)
    in
    let pointer_start = max 1 start_col in
    let pointer_end = max pointer_start end_col in
    let leading_spaces =
      String.make (pointer_start + String.length line_indicator - 1) ' '
    in
    let marker = String.make (pointer_end - pointer_start + 1) '~' in
    leading_spaces ^ marker
  in
  let rec build line_number acc =
    if line_number > end_line
    then String.concat "\n" (List.rev acc)
    else begin
      let line_text =
        match List.nth_opt lines (line_number - 1) with
        | Some text -> text
        | None -> ""
      in
      let formatted = Printf.sprintf "%d | %s" line_number line_text in
      let acc =
        if line_number >= span.start_pos.line && line_number <= span.end_pos.line
        then pointer_line line_number line_text :: formatted :: acc
        else formatted :: acc
      in
      build (line_number + 1) acc
    end
  in
  build start_line []
;;

let display_span source_code (span : span) = display_multiline_span source_code span
