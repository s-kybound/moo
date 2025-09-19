{
    open Parser
    open Lexing

    type loc = { start: position; stop: position }
    exception Lexing_error of loc * string

    let curr_loc lexbuf =
        { start = lexeme_start_p lexbuf; stop = lexeme_end_p lexbuf }

    let raisef lexbuf fmt =
        Printf.kprintf (fun msg -> raise (Lexing_error (curr_loc lexbuf, msg))) fmt

    let keywords : (string, Parser.token) Hashtbl.t =
        let h = Hashtbl.create 2 in
        Hashtbl.replace h "letcc" LETC;
        Hashtbl.replace h "let"   LETP;
        h

    let verify_ident _lexbuf id =
        match Hashtbl.find_opt keywords id with
        | Some t -> t
        | None   -> IDENT id

    let verify_coident lexbuf cid =
        let name = String.sub cid 1 (String.length cid - 1) in
        match Hashtbl.find_opt keywords name with
        | Some _ -> raisef lexbuf "%s is a reserved syntactic keyword and cannot be used as a covariable" name
        | None      -> COIDENT name
}

let hspace         = [' ' '\t' '\r']+
let newline = '\n'
let digit              = ['0'-'9']
let letter             = ['A'-'Z' 'a'-'z']
let special_initial    = ['!' '$' '%' '&' '*' '/' ':' '<' '=' '>' '?' '^' '_' '~']
let initial            = letter | special_initial
let special_subsequent = ['+' '-' '.' '@']
let subsequent         = initial | digit | special_subsequent

let ident = initial subsequent*
let coident = '\'' ident

rule token = parse
  | hspace                     { token lexbuf }
  | newline  { Lexing.new_line lexbuf; token lexbuf }
  | "(*"                            { skip_comment 1 lexbuf; token lexbuf }
  | "*)"                            { raisef lexbuf "Unexpected unmatched *)" }
  | "#*"                            { skip_datum lexbuf; token lexbuf }
  | '['                             { LBRACK }
  | ']'                             { RBRACK }
  | '('                             { LPAREN }
  | ')'                             { RPAREN }
  | coident as cid { verify_coident lexbuf cid }
  | ident as id       { verify_ident lexbuf id }
  | eof                             { EOF }
  | _ as ch                         { raisef lexbuf "Unexpected char while parsing: %C" ch }

and skip_datum = parse
  | hspace                      { skip_datum lexbuf }
  | newline                     { Lexing.new_line lexbuf; skip_datum lexbuf }
  | "(*"                        { skip_comment 1 lexbuf; skip_datum lexbuf }
  | "#*"                        { skip_datum lexbuf; skip_datum lexbuf }
  | '('                         { skip_parens 1 lexbuf }
  | '['                         { skip_bracks 1 lexbuf }
  | coident                     { () }
  | ident                       { () }
  | eof                         { raisef lexbuf "Datum comment did not consume anything" }
  | _ as ch                     { raisef lexbuf "Unexpected char while evaluating datum comment: %C" ch }

and skip_parens depth = parse
  | hspace                      { skip_parens depth lexbuf }
  | newline                     { Lexing.new_line lexbuf; skip_parens depth lexbuf }
  | "(*"                        { skip_comment 1 lexbuf; skip_parens depth lexbuf }
  | "#*"                         { skip_datum lexbuf; skip_parens depth lexbuf }
  | '('                          { skip_parens (depth + 1) lexbuf }
  | ')'                          { if depth = 1 then () else skip_parens (depth - 1) lexbuf }
  | '['                          { skip_bracks 1 lexbuf; skip_parens depth lexbuf }
  | coident          { skip_parens depth lexbuf }
  | ident     { skip_parens depth lexbuf }
  | eof                          { raisef lexbuf "Unterminated (...) in datum comment" }
  | _ as ch                      { raisef lexbuf "Unexpected char while evaluating datum comment: %C" ch }

and skip_bracks depth = parse
  | hspace                      { skip_bracks depth lexbuf }
  | newline                     { Lexing.new_line lexbuf; skip_bracks depth lexbuf }
  | "(*"                        { skip_comment 1 lexbuf; skip_bracks depth lexbuf }
  | "#*"                         { skip_datum lexbuf; skip_bracks depth lexbuf }
  | '['                          { skip_bracks (depth + 1) lexbuf }
  | ']'                          { if depth = 1 then () else skip_bracks (depth - 1) lexbuf }
  | '('                          { skip_parens 1 lexbuf; skip_bracks depth lexbuf }
  | coident     { skip_bracks depth lexbuf }
  | ident          { skip_bracks depth lexbuf }
  | eof                          { raisef lexbuf "Unterminated [...] in datum comment" }
  | _ as ch                      { raisef lexbuf "Unexpected char while evaluating datum comment: %C" ch }

and skip_comment depth = parse
  | hspace                    { skip_comment depth lexbuf }
  | newline                     { Lexing.new_line lexbuf; skip_comment depth lexbuf }
  | "(*" { skip_comment (depth + 1) lexbuf }
  | "*)" { if depth = 1 then () else skip_comment (depth - 1) lexbuf }
  | eof { raisef lexbuf "Unenclosed (*"}
  | _ { skip_comment depth lexbuf }