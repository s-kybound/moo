{
  open Parser
  open Parser_error.Lexer

  let keywords : (string, Parser.token) Hashtbl.t =
    let keywords : (string * Parser.token) list = [
      ("letcc",   LETC);
      ("let",     LETP);
      ("pair",    PAIR);
      ("split",   SPLIT);
      ("copair",  COPAIR);
      ("cosplit", COSPLIT);
      ("in",      IN)
    ] in
    keywords
    |> List.to_seq
    |> Hashtbl.of_seq

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

let hspace             = [' ' '\t' '\r']+
let newline            = '\n'
let digit              = ['0'-'9']
let letter             = ['A'-'Z' 'a'-'z']
let special_initial    = ['_']
let initial            = letter | special_initial
let subsequent         = initial | digit

let ident = initial subsequent*
let coident = '\'' ident

rule token = parse
  | hspace         { token lexbuf }
  | newline        { Lexing.new_line lexbuf; token lexbuf }
  | "(*"           { skip_comment 1 lexbuf; token lexbuf }
  | "*)"           { raisef lexbuf "Unmatched *). Was a comment erased incorrectly?" }
  | "->"           { LTRARROW }
  | "<-"           { RTLARROW }
  | '['            { LBRACK }
  | ']'            { RBRACK }
  | '('            { LPAREN }
  | ')'            { RPAREN }
  | coident as cid { verify_coident lexbuf cid }
  | ident as id    { verify_ident lexbuf id }
  | eof            { EOF }
  | _ as ch        { raisef lexbuf "Unexpected char while parsing: %C" ch }

and skip_comment depth = parse
  | hspace         { skip_comment depth lexbuf }
  | newline        { Lexing.new_line lexbuf; skip_comment depth lexbuf }
  | "(*"           { skip_comment (depth + 1) lexbuf }
  | "*)"           { if depth = 1 then () else skip_comment (depth - 1) lexbuf }
  | eof            { raisef lexbuf "Unterminated (*...*) comment" }
  | _              { skip_comment depth lexbuf }
