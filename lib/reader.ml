open Lexing

let with_filename buffer name =
  buffer.lex_curr_p <- { buffer.lex_curr_p with pos_fname = name }; buffer

let run program_buffer = Parser.entrypoint Lexer.token program_buffer

let of_channel ~filename ic =
  let lb = with_filename (Lexing.from_channel ic) filename in
  run lb

let of_string ?(filename = "<string>") s =
  let lb = with_filename (Lexing.from_string s) filename in
  run lb

let of_file filename =
  let ic = open_in filename in
  Fun.protect
    ~finally:(fun () -> close_in_noerr ic)
    (fun () -> of_channel ~filename ic)

