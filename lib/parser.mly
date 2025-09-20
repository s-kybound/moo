%{  
  type loc = { start: Lexing.position; stop: Lexing.position } [@@warning "-69"]
  exception Parsing_error of loc * string
  
  let here start stop msg = raise (Parsing_error ({start; stop}, msg))
%}

%token LBRACK RBRACK LPAREN RPAREN
%token LETC LETP (* mu, mu-tilde abstactions *)
%token PAIR SPLIT (* pair producer and its split consumer *)
%token COSPLIT COPAIR (* cosplit producer and its copair consumer *)
(*
%token LEFTP RIGHTP CASE (* sum producers, case consumers *)
%token COCASE LEFTC RIGHTC (* cocase producer, sum consumers *)
*)
%token <string> IDENT
%token <string> COIDENT
%token EOF
%start <Ast.Surface.t> entrypoint
%%

entrypoint: p=program                   { p }

program: 
  | c=cut EOF                           { c }
  | EOF                                 { here $startpos($1) $endpos($1) "File is empty." }
  | error                               { here $startpos $endpos "Unexpected syntax error before end of file" }

cut: 
  | LBRACK p=producer c=consumer RBRACK { Ast.Surface.cut p c }
  | LBRACK producer consumer error      { here $startpos($1) $endpos($3) "cut: expected closing ']' in '[ <producer> <consumer> ...'" }
  | LBRACK consumer error               { here $startpos($1) $endpos($2) "cut: expected producer in '[ <producer> <consumer> ...'" }
  | LBRACK producer error               { here $startpos($1) $endpos($2) "cut: expected consumer in '[ <producer> ...'" }
  | LBRACK error                        { here $startpos($1) $endpos($1) "cut: expected producer in '[ ...'" }
  | RBRACK                              { here $startpos($1) $endpos($1) "cut: unmatched ']'" }

producer:
  | v = IDENT                           { Ast.Surface.variable v }
  | LPAREN LETC cv=COIDENT c=cut RPAREN { Ast.Surface.mu cv c }
  | LPAREN LETC COIDENT cut error       { here $startpos($1) $endpos($4) "letcc: expected closing ')' in '(letcc <covariable> <cut> ...'" }
  | LPAREN LETC COIDENT error           { here $startpos($1) $endpos($3) "letcc: expected cut in '(letcc <covariable> ...'"}
  | LPAREN LETC IDENT error             { here $startpos($1) $endpos($3) "letcc: letcc expects a covariable, not a variable"}
  | LPAREN LETC error                   { here $startpos($1) $endpos($2) "letcc: expected covariable in '(letcc ...'"}
  | LPAREN error                        { here $startpos($1) $endpos($1) "expected letcc abstraction"}
  | RPAREN                              { here $startpos($1) $endpos($1) "letcc: unmatched ')'" }

consumer: 
  | cv = COIDENT                        { Ast.Surface.covariable cv }
  | LPAREN LETP v=IDENT c=cut RPAREN    { Ast.Surface.mutilde v c }
  | LPAREN LETP IDENT cut error         { here $startpos($1) $endpos($4) "let: expected closing ')' in '(let <variable> <cut> ...'" }
  | LPAREN LETP IDENT error             { here $startpos($1) $endpos($3) "let: expected cut in '(let <variable> ...'" }
  | LPAREN LETP COIDENT error           { here $startpos($1) $endpos($3) "let: let expects a variable, not a covariable" }
  | LPAREN LETP error                   { here $startpos($1) $endpos($2) "let: expected variable in '(let ...'" }
  | LPAREN error                        { here $startpos($1) $endpos($1) "expected let abstraction" }
  | RPAREN                              { here $startpos($1) $endpos($1) "let: unmatched ')'" }
