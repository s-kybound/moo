{
  open Parser

  let raisef lexbuf fmt =
    Printf.ksprintf
      (fun msg ->
         let pos = Lexing.lexeme_start_p lexbuf in
         let line = pos.Lexing.pos_lnum in
         let col = pos.Lexing.pos_cnum - pos.Lexing.pos_bol + 1 in
         failwith (Printf.sprintf "Lexing error at line %d, column %d: %s" line col msg))
      fmt

  let keywords : (string, Parser.token) Hashtbl.t =
    let keywords : (string * Parser.token) list = [
      ("let",     LET);
      ("in",      IN);
      ("rec",     REC);
      ("match",   MATCH);
      ("data",    DATA);
      ("codata",  CODATA);
      ("done",    DONE);
      ("proc",    PROC); 
      ("cbv",     CBV);
      ("cbn",     CBN);   
      ("type",    TYPE);
      ("unit",    UNIT);
      ("raw64",   RAW64);
      ("_",       UNDERSCORE);
      (* ("unpack",  UNPACK);
      ("pack",    PACK);
      ("gen",     GEN);
      ("inst",    INST);
      ("forall",  FORALL);
      ("exists",  EXISTS); *)
    ] in
    keywords
    |> List.to_seq
    |> Hashtbl.of_seq

  let verify_ident _lexbuf id =
    match Hashtbl.find_opt keywords id with
    | Some t -> t
    | None   -> IDENT id
}

let hspace             = [' ' '\t' '\r']+
let newline            = '\n'
let digit              = ['0'-'9']
let capital            = ['A'-'Z']
let lowercase          = ['a'-'z']
let letter             = capital | lowercase
let special_initial    = ['_']
let initial            = letter | special_initial
let subsequent         = initial | digit

let number = '-'? digit+

let ident = initial subsequent*
let constructor_ident = capital subsequent*

rule token = parse
  | hspace+                   { token lexbuf }
  | newline+                  { Lexing.new_line lexbuf; token lexbuf }
  | "/*"                      { skip_comment 1 lexbuf; token lexbuf }
  | "*/"                      { raisef lexbuf "Unmatched */. Was a comment erased incorrectly?" }
  | "//"                      { skip_line lexbuf; token lexbuf }
  | "->"                      { LTRARROW }
  | "<-"                      { RTLARROW }
  | '='                       { EQUALS }
  | "::"                      { DOUBLECOLON }
  | ':'                       { COLON }
  | ";"                       { DELIMITER }
  | '['                       { LBRACK }
  | ']'                       { RBRACK }
  | '('                       { LPAREN }
  | ')'                       { RPAREN }
  | '{'                       { LBRACE }
  | '}'                       { RBRACE }
  | '<'                       { LANGLE }
  | '>'                       { RANGLE }
  | '.'                       { DOT }
  | ','                       { COMMA }
  | '|'                       { BAR }
  | '+'                       { PLUS }
  | '-'                       { MINUS }
  | '~'                       { NEG }
  | '\\'                      { token lexbuf } (* skip a line just like C *)
  | number as num             { NUMBER (Int64.of_string num) }
  (* TODO: find a nicer way to handle parser conflicts than this *)
  | constructor_ident as cid '('  
                              { CONSTRUCTOR_LPAREN cid }
  | constructor_ident as cid  { CONSTRUCTOR_IDENT cid }
  | ident as id               { verify_ident lexbuf id }
  | eof                       { EOF }
  | _ as ch                   { raisef lexbuf "Unexpected char while parsing: %C" ch }

and skip_comment depth = parse
  | hspace         { skip_comment depth lexbuf }
  | newline        { Lexing.new_line lexbuf; skip_comment depth lexbuf }
  | "/*"           { skip_comment (depth + 1) lexbuf }
  | "*/"           { if depth = 1 then () else skip_comment (depth - 1) lexbuf }
  | eof            { raisef lexbuf "Unterminated /*...*/ comment" }
  | _              { skip_comment depth lexbuf }

and skip_line = parse
  | newline        { Lexing.new_line lexbuf }
  | eof            { () }
  | _              { skip_line lexbuf }
