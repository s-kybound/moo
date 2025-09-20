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
nice to have, but we are trying to prove minimality with negation
and conjuction alone for now

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
(*
  | LPAREN X error                      { here $startpos($1) $endpos($2) "expected closing ')'" }
  | LPAREN error                        { here $startpos($1) $endpos($1) "expected expression after '('" }
  | RPAREN                              { here $startpos($1) $endpos($1) "unmatched ')'" }
*)
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
  | v = IDENT                           { Ast.Surface.Identifier.name v }

letc_body:
  | LETC cv=cval c=cut                  { Ast.Surface.Producer.mu cv c }
  | LETC COIDENT error                  { here $startpos($1) $endpos($2) "letcc: expected cut in '(letcc <covariable> ...'" }
  | LETC IDENT error                    { here $startpos($1) $endpos($2) "letcc: letcc expects a covariable, not a variable" }
  | LETC error                          { here $startpos($1) $endpos($1) "letcc: expected covariable in '(letcc ...'" }

letc:
  | parens(letc_body)                   { $1 }

product_body:
  | PAIR a=either b=either              { Ast.Surface.Producer.pair a b }
  | PAIR either error                   { here $startpos($1) $endpos($2) "pair: expected second element in (pair <a> ..." } 
  | PAIR error                          { here $startpos($1) $endpos($2) "pair: expected an element in (pair ..." } 

product:
  | parens(product_body)                { $1 }

cosplit_body:
  | COSPLIT a=either_identifier 
            b=either_identifier 
            c=cut                       { Ast.Surface.Producer.cosplit a b c }

cosplit:
  | parens(cosplit_body)                { $1 }

producer:
  | p=pval                              { Ast.Surface.Producer.variable p }
  | letc                                { $1 }
  | product                             { $1 }
  | cosplit                             { $1 }

cval:
  | cv = COIDENT                        { Ast.Surface.Identifier.coname cv }

letp_body:
  | LETP v=pval c=cut                   { Ast.Surface.Consumer.mutilde v c }
  | LETP IDENT error                    { here $startpos($1) $endpos($2) "let: expected cut in '(let <variable> ...'" }
  | LETP COIDENT error                  { here $startpos($1) $endpos($2) "let: let expects a variable, not a covariable" }
  | LETP error                          { here $startpos($1) $endpos($1) "let: expected variable in '(let ...'" }

letp:
  | parens(letp_body)                   { $1 }

split_body:
  | SPLIT a=either_identifier 
          b=either_identifier 
          c=cut                         { Ast.Surface.Consumer.split a b c }

split:
  | parens(split_body)                  { $1 }

coproduct_body:
  | COPAIR a=either b=either            { Ast.Surface.Consumer.copair a b }
  | COPAIR either error                 { here $startpos($1) $endpos($2) "copair: expected second element in (copair <a> ..." } 
  | COPAIR error                        { here $startpos($1) $endpos($2) "copair: expected an element in (copair ..." } 

coproduct:
  | parens(coproduct_body)              { $1 }

consumer: 
  | c=cval                              { Ast.Surface.Consumer.covariable c }
  | letp                                { $1 }
  | split                               { $1 }
  | coproduct                           { $1 }

either:
  | p=producer                          { Ast.Surface.Positive p }
  | c=consumer                          { Ast.Surface.Negative c }

either_identifier:
  | pval                                { Ast.Surface.Positive_name $1 }
  | cval                                { Ast.Surface.Negative_name $1 }
