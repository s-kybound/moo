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

parens(X):
  | LPAREN x=X RPAREN                   { x }
  | LPAREN X error                      { here $startpos($1) $endpos($2) "expected closing ')'" }
  | LPAREN error                        { here $startpos($1) $endpos($1) "expected expression after '('" }
  | RPAREN                              { here $startpos($1) $endpos($1) "unmatched ')'" }

bracks(X):
  | LBRACK x=X RBRACK                   { x }
  | LBRACK X error                      { here $startpos($1) $endpos($2) "expected closing ']'" }
  | LBRACK error                        { here $startpos($1) $endpos($1) "expected expression after '['" }
  | RBRACK                              { here $startpos($1) $endpos($1) "unmatched ']'" }

program: 
  | c=cut EOF                           { c }
  | EOF                                 { here $startpos($1) $endpos($1) "File is empty." }

cut_body:
  | p=producer c=consumer               { Ast.Surface.cut p c }
  | consumer error                      { here $startpos($1) $endpos($1) "cut: expected producer in '[ <producer> <consumer> ...'" }

cut: 
  | bracks(cut_body)                    { $1 }

pval:
  | v = IDENT                           { Ast.Surface.variable v }

letc_body:
  | LETC cv=COIDENT c=cut               { Ast.Surface.mu cv c }
  | LETC COIDENT error                  { here $startpos($1) $endpos($2) "letcc: expected cut in '(letcc <covariable> ...'"}
  | LETC IDENT error                    { here $startpos($1) $endpos($2) "letcc: letcc expects a covariable, not a variable"}
  | LETC error                          { here $startpos($1) $endpos($1) "letcc: expected covariable in '(letcc ...'"}

letc:
  | parens(letc_body)                   { $1 }

producer:
  | pval                                { $1 }
  | letc                                { $1 }

cval:
  | cv = COIDENT                        { Ast.Surface.covariable cv }

letp_body:
  | LETP v=IDENT c=cut                  { Ast.Surface.mutilde v c }
  | LETP IDENT error                    { here $startpos($1) $endpos($2) "let: expected cut in '(let <variable> ...'" }
  | LETP COIDENT error                  { here $startpos($1) $endpos($2) "let: let expects a variable, not a covariable" }
  | LETP error                          { here $startpos($1) $endpos($1) "let: expected variable in '(let ...'" }

letp:
  | parens(letp_body)                   { $1 }

consumer: 
  | cval                                { $1 }
  | letp                                { $1 }
