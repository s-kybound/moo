open Lexing

type loc =
  { start : position
  ; stop : position
  }

module Lexer = struct
  exception Lexing_error of loc * string

  let curr_loc lexbuf = { start = lexeme_start_p lexbuf; stop = lexeme_end_p lexbuf }

  let raisef lexbuf fmt =
    Printf.kprintf (fun msg -> raise (Lexing_error (curr_loc lexbuf, msg))) fmt
  ;;
end

module Parser = struct
  exception Parsing_error of loc * string

  let raisef start stop fmt =
    Printf.kprintf (fun msg -> raise (Parsing_error ({ start; stop }, msg))) fmt
  ;;
end
