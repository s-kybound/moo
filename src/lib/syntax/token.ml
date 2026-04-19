open Parser

(* Centralised keyword table for lexer and token->string mapping *)

let table : (string, Parser.token) Hashtbl.t = Hashtbl.create 64

let keywords =
  [ "do", DO
  ; "let", LET
  ; "in", IN
  ; "rec", REC
  ; "match", MATCH
  ; "data", DATA
  ; "codata", CODATA
  ; "exit", EXIT
  ; "proc", PROC
  ; "cbv", CBV
  ; "cbn", CBN
  ; "type", TYPE
  ; "unit", UNIT
  ; "int", INT
  ; "true", TRUE
  ; "false", FALSE
  ; "bool", BOOL
    (* ; "open", OPEN *)
    (* ; "module", MODULE *)
  ; "use", USE
  ; "as", AS
  ; "abstract", ABSTRACT
  ; "_", UNDERSCORE
  ]
;;

let () = List.iter (fun (s, t) -> Hashtbl.add table s t) keywords
let keyword_of_string s = Hashtbl.find_opt table s

let string_of_keyword tok =
  let rev_tbl =
    lazy
      (let r = Hashtbl.create 64 in
       Hashtbl.iter
         (fun k v ->
            match v with
            | Parser.IDENT _ | Parser.NUMBER _ -> ()
            | _ -> Hashtbl.replace r v k)
         table;
       r)
  in
  Hashtbl.find_opt (Lazy.force rev_tbl) tok
;;

let symbols =
  [ IDENT "<identifier>"
  ; NAMESPACE_IDENT "<identifier>"
  ; CONSTRUCTOR_IDENT "<constructor identifier>"
  ; CONSTRUCTOR_LPAREN "<constructor identifier with parens>"
  ; LBRACK
  ; RBRACK
  ; LPAREN
  ; RPAREN
  ; LBRACE
  ; RBRACE
  ; LANGLE
  ; RANGLE
  ; LTRARROW
  ; RTLARROW
  ; EQUALS
  ; DELIMITER
  ; COLON
  ; PLUS
  ; MINUS
  ; NEG
  ; STAR
  ; SLASH
  ; PERCENT
  ; BAR
  ; DOT
  ; COMMA
  ; EOF
  ]
;;

let tokens = symbols @ List.map snd keywords

let string_of_token = function
  | DO -> "do"
  | LET -> "let"
  | IN -> "in"
  | REC -> "rec"
  | MATCH -> "match"
  | DATA -> "data"
  | CODATA -> "codata"
  | EXIT -> "exit"
  | PROC -> "proc"
  | CBV -> "cbv"
  | CBN -> "cbn"
  | TYPE -> "type"
  | UNIT -> "unit"
  | INT -> "int"
  | TRUE -> "true"
  | FALSE -> "false"
  | BOOL -> "bool"
  (* | OPEN -> "open" *)
  (* | MODULE -> "module" *)
  | USE -> "use"
  | AS -> "as"
  | ABSTRACT -> "abstract"
  | UNDERSCORE -> "_"
  | STAR -> "*"
  | LTRARROW -> "->"
  | RTLARROW -> "<-"
  | EQUALS -> "="
  | COLON -> ":"
  | DELIMITER -> ";;"
  | LBRACK -> "["
  | RBRACK -> "]"
  | LPAREN -> "("
  | RPAREN -> ")"
  | LBRACE -> "{"
  | RBRACE -> "}"
  | LANGLE -> "<"
  | RANGLE -> ">"
  | DOT -> "."
  | COMMA -> ","
  | BAR -> "|"
  | PLUS -> "+"
  | MINUS -> "-"
  | NEG -> "~"
  | SLASH -> "/"
  | PERCENT -> "%"
  | EOF -> "EOF"
  | NUMBER _ -> "<number>"
  | IDENT _ | NAMESPACE_IDENT _ -> "<identifier>"
  | CONSTRUCTOR_IDENT _ -> "<constructor identifier>"
  | CONSTRUCTOR_LPAREN _ -> "<constructor identifier followed by paren>"
;;
