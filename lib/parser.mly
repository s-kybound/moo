%{  
  open Parser_error.Parser
%}

%token <string> IDENT
%token LBRACK RBRACK LPAREN RPAREN
%token LETC LETP (* mu, mu-tilde abstactions *)
%token PAIR SPLIT (* pair producer and its split consumer *)
%token COSPLIT COPAIR (* cosplit producer and its copair consumer *)
%token LTRARROW RTLARROW IN (* statement syntax *)
%token DEFC DEFP (* top-level definitions *)
%token EQUALS DELIMITER (* top-level definitions *)
%token COLON (* type binder annotation *)
%token EOF
%start <Ast.Surface.t> entrypoint
%%

entrypoint: p=program                   { p }

program: 
  | definitions=top_level_definition* 
    main=statement EOF                  { Ast.Surface.program definitions main }
  | definitions=top_level_definition* 
    EOF                                 { Ast.Surface.program
                                          definitions
                                          (Ast.Surface.cut 
                                            (Ast.Surface.Producer.variable (Ast.Surface.Identifier.name "no_main")) 
                                            (Ast.Surface.Consumer.covariable (Ast.Surface.Identifier.coname "halt")))
                                        }
  | LPAREN error                        { raisef $startpos($1) $endpos($1) "unexpected '(' - missing closing ')' or malformed expression" }
  | RPAREN error                        { raisef $startpos($1) $endpos($1) "unexpected ')' - no matching '(' found" }

top_level_definition:
  | DEFP   name=pval 
           input=cval 
    EQUALS body=statement DELIMITER     { Ast.Surface.defp name input body }
  | DEFC   coname=cval 
           input=pval 
    EQUALS body=statement DELIMITER     { Ast.Surface.defc coname input body }

(* Nested statements *)
statement:
  | LETP v=pval 
    RTLARROW p=producer IN m=statement  { Ast.Surface.cut
                                            p
                                            (Ast.Surface.Consumer.mutilde v m)
                                        }
  | LETC cv=cval 
    RTLARROW c=consumer IN m=statement  { Ast.Surface.cut
                                            (Ast.Surface.Producer.mu cv m)
                                            c
                                        }
  | SPLIT    a=either_identifier 
             b=either_identifier        
    RTLARROW p=producer IN m=statement  { Ast.Surface.cut
                                            p
                                            (Ast.Surface.Consumer.split a b m)
                                        }
  | COSPLIT  a=either_identifier 
             b=either_identifier        
    RTLARROW c=consumer IN m=statement  { Ast.Surface.cut
                                            (Ast.Surface.Producer.cosplit a b m)
                                            c
                                        }
  | cut                                 { $1 }

cut_body:
  | p=producer c=consumer               { Ast.Surface.cut p c }
  | producer producer error             { raisef $startpos($1) $endpos($2) "cut syntax error: found two producers, expected [producer consumer]" }
  | consumer consumer error             { raisef $startpos($1) $endpos($2) "cut syntax error: found two consumers, expected [producer consumer]" }
  | producer error                      { raisef $startpos($1) $endpos($1) "incomplete cut: expected consumer after producer in [%s ...]" (Ast.Surface.Show.show_producer $1) }
  | consumer error                      { raisef $startpos($1) $endpos($1) "incomplete cut: expected producer before consumer in [... %s]" (Ast.Surface.Show.show_consumer $1) }

cut: 
  | LBRACK c=cut_body RBRACK            { c }
  | LBRACK cut_body error               { raisef $startpos($1) $endpos($2) "unclosed cut: expected ']' to close cut started here" }
  | LBRACK error                        { raisef $startpos($1) $endpos($1) "empty cut: expected [producer consumer] after '['" }
  | RBRACK                              { raisef $startpos($1) $endpos($1) "unmatched ']': no corresponding '[' found" }

pval:
  | v = IDENT                           { Ast.Surface.Identifier.name v }

letc_body:
  | LETC cv=cval LTRARROW s=statement   { Ast.Surface.Producer.mu cv s }
  | LETC IDENT error                    { raisef $startpos($1) $endpos($2) "incomplete letcc: expected cut after covariable '%s'" $2 }
  | LETC error                          { raisef $startpos($1) $endpos($1) "incomplete letcc: expected covariable after 'letcc'" }

letc:
  | LPAREN l=letc_body RPAREN           { l }
  | LPAREN letc_body error              { raisef $startpos($1) $endpos($2) "unclosed letcc: expected ')' to close expression started here" }

product_body:
  | PAIR a=either b=either              { Ast.Surface.Producer.pair a b }
  | PAIR either error                   { raisef $startpos($1) $endpos($2) "incomplete pair: expected second element after first element" } 
  | PAIR error                          { raisef $startpos($1) $endpos($1) "incomplete pair: expected two elements like (pair x y)" } 

product:
  | LPAREN p=product_body RPAREN        { p }
  | LPAREN product_body error           { raisef $startpos($1) $endpos($2) "unclosed pair: expected ')' to close pair started here" }

cosplit_body:
  | COSPLIT  a=either_identifier 
             b=either_identifier 
    LTRARROW s=statement                { Ast.Surface.Producer.cosplit a b s }
  | COSPLIT either_identifier 
            either_identifier error     { raisef $startpos($1) $endpos($3) "incomplete cosplit: expected cut after variables" }
  | COSPLIT either_identifier error     { raisef $startpos($1) $endpos($2) "incomplete cosplit: expected second variable and cut" }
  | COSPLIT error                       { raisef $startpos($1) $endpos($1) "incomplete cosplit: expected (cosplit var1 var2 cut)" }

cosplit:
  | LPAREN c=cosplit_body RPAREN        { c }
  | LPAREN cosplit_body error           { raisef $startpos($1) $endpos($2) "unclosed cosplit: expected ')' to close expression started here" }

producer:
  | p=pval                              { Ast.Surface.Producer.variable p }
  | letc                                { $1 }
  | product                             { $1 }
  | cosplit                             { $1 }

cval:
  | cv = IDENT                        { Ast.Surface.Identifier.coname cv }

letp_body:
  | LETP v=pval LTRARROW s=statement    { Ast.Surface.Consumer.mutilde v s }
  | LETP IDENT error                    { raisef $startpos($1) $endpos($2) "incomplete let: expected cut after variable '%s'" $2 }
  | LETP error                          { raisef $startpos($1) $endpos($1) "incomplete let: expected variable after 'let'" }

letp:
  | LPAREN l=letp_body RPAREN           { l }
  | LPAREN letp_body error              { raisef $startpos($1) $endpos($2) "unclosed let: expected ')' to close expression started here" }

split_body:
  | SPLIT    a=either_identifier 
             b=either_identifier 
    LTRARROW s=statement                { Ast.Surface.Consumer.split a b s }
  | SPLIT either_identifier 
          either_identifier error       { raisef $startpos($1) $endpos($3) "incomplete split: expected cut after variables" }
  | SPLIT either_identifier error       { raisef $startpos($1) $endpos($2) "incomplete split: expected second variable and cut" }
  | SPLIT error                         { raisef $startpos($1) $endpos($1) "incomplete split: expected (split var1 var2 cut)" }

split:
  | LPAREN s=split_body RPAREN          { s }
  | LPAREN split_body error             { raisef $startpos($1) $endpos($2) "unclosed split: expected ')' to close expression started here" }

coproduct_body:
  | COPAIR a=either b=either            { Ast.Surface.Consumer.copair a b }
  | COPAIR either error                 { raisef $startpos($1) $endpos($2) "incomplete copair: expected second element after first element" } 
  | COPAIR error                        { raisef $startpos($1) $endpos($1) "incomplete copair: expected two elements like (copair x y)" } 

coproduct:
  | LPAREN c=coproduct_body RPAREN      { c }
  | LPAREN coproduct_body error         { raisef $startpos($1) $endpos($2) "unclosed copair: expected ')' to close expression started here" }

consumer: 
  | c=cval                              { Ast.Surface.Consumer.covariable c }
  | letp                                { $1 }
  | split                               { $1 }
  | coproduct                           { $1 }
  | error                               { raisef $startpos $endpos "syntax error: expected consumer (covariable, let, split, or copair)" }

either:
  | p=producer                          { Ast.Surface.Positive p }
  | c=consumer                          { Ast.Surface.Negative c }

either_identifier:
  | pval                                { Ast.Surface.Positive_name $1 }
  | cval                                { Ast.Surface.Negative_name $1 }
