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

program: 
  | c=cut EOF                           { c }
  | EOF                                 { 
                                          Ast.Surface.cut 
                                            (Ast.Surface.Producer.variable (Ast.Surface.Identifier.name "empty-file")) 
                                            (Ast.Surface.Consumer.covariable (Ast.Surface.Identifier.coname "halt")) 
                                        }
  | LPAREN error                        { here $startpos($1) $endpos($1) "unexpected '(' - mismatched or misplaced parenthesis" }
  | RPAREN error                        { here $startpos($1) $endpos($1) "unexpected ')' - mismatched or misplaced parenthesis" }

cut_body:
  | p=producer c=consumer               { Ast.Surface.cut p c }
  | consumer error                      { here $startpos($1) $endpos($1) "cut: expected producer in '[ <producer> <consumer> ...'" }

cut: 
  | LBRACK c=cut_body RBRACK            { c }
  | LBRACK cut_body error               { here $startpos($1) $endpos($2) "cut: expected closing ']'"}
  | LBRACK error                        { here $startpos($1) $endpos($1) "expected cut after '['" }
  | RBRACK                              { here $startpos($1) $endpos($1) "expected cut, got unmatched ']'" }

pval:
  | v = IDENT                           { Ast.Surface.Identifier.name v }

letc_body:
  | LETC cv=cval c=cut                  { Ast.Surface.Producer.mu cv c }
  | LETC COIDENT error                  { here $startpos($1) $endpos($2) "letcc: expected cut in '(letcc <covariable> ...'" }
  | LETC IDENT error                    { here $startpos($1) $endpos($2) "letcc: letcc expects a covariable, not a variable" }
  | LETC error                          { here $startpos($1) $endpos($1) "letcc: expected covariable in '(letcc ...'" }

letc:
  | LPAREN l=letc_body RPAREN           { l }
  | LPAREN letc_body error              { here $startpos($1) $endpos($2) "letcc: expected closing ')'"}

product_body:
  | PAIR a=either b=either              { Ast.Surface.Producer.pair a b }
  | PAIR either error                   { here $startpos($1) $endpos($2) "pair: expected second element in (pair <a> ..." } 
  | PAIR error                          { here $startpos($1) $endpos($2) "pair: expected an element in (pair ..." } 

product:
  | LPAREN p=product_body RPAREN        { p }
  | LPAREN product_body error           { here $startpos($1) $endpos($2) "pair: expected closing ')'"}

cosplit_body:
  | COSPLIT a=either_identifier 
            b=either_identifier 
            c=cut                       { Ast.Surface.Producer.cosplit a b c }

cosplit:
  | LPAREN c=cosplit_body RPAREN        { c }
  | LPAREN cosplit_body error           { here $startpos($1) $endpos($2) "cosplit: expected closing ')'" }

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
  | LPAREN l=letp_body RPAREN           { l }
  | LPAREN letp_body error              { here $startpos($1) $endpos($2) "let: expected closing ')'"}

split_body:
  | SPLIT a=either_identifier 
          b=either_identifier 
          c=cut                         { Ast.Surface.Consumer.split a b c }

split:
  | LPAREN s=split_body RPAREN          { s }
  | LPAREN split_body error             { here $startpos($1) $endpos($2) "split: expected closing ')'" }

coproduct_body:
  | COPAIR a=either b=either            { Ast.Surface.Consumer.copair a b }
  | COPAIR either error                 { here $startpos($1) $endpos($2) "copair: expected second element in (copair <a> ..." } 
  | COPAIR error                        { here $startpos($1) $endpos($2) "copair: expected an element in (copair ..." } 

coproduct:
  | LPAREN c=coproduct_body RPAREN      { c }
  | LPAREN coproduct_body error         { here $startpos($1) $endpos($2) "copair: expected closing ')'"}

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
