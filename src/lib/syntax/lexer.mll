{
  open Parser
  open Error

  let raisef lexbuf fmt =
    Printf.ksprintf
      (fun message ->
        let span = Some (Loc_utils.get_lexing_span lexbuf) in
        raise (SyntaxError 
                { span
                ; message
                })) 
      fmt

  let verify_ident _lexbuf id =
    match Token.keyword_of_string id with
    | Some t -> t
    | None -> IDENT id
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
let any_ident = ident | constructor_ident

let namespace_sep     = "::"

rule token = parse
  | hspace+                   { token lexbuf }
  | newline+                  { Lexing.new_line lexbuf; token lexbuf }
  | "//"                      { skip_line lexbuf; token lexbuf }
  | "/*"                      { skip_comment 1 lexbuf; token lexbuf }
  | "*/"                      { raisef lexbuf "Unmatched */.`" }
  | "->"                      { LTRARROW }
  | "<-"                      { RTLARROW }
  | '='                       { EQUALS }
  | ':'                       { COLON }
  | ";;"                      { DELIMITER }
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
  | '*'                       { STAR }
  | '/'                       { SLASH }
  | '%'                       { PERCENT }
  | number as num             { NUMBER (Int64.of_string num) }
  (* TODO: find a nicer way to handle parser conflicts than these few rules *)
  | any_ident as ns_id namespace_sep  
                              { NAMESPACE_IDENT ns_id }
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
