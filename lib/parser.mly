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
                                            (Ast.Surface.Name "no_main")
                                            (Ast.Surface.Name "'halt"))
                                        }
  | LPAREN error                        { raisef $startpos($1) $endpos($1) "unexpected '(' - missing closing ')' or malformed expression" }
  | RPAREN error                        { raisef $startpos($1) $endpos($1) "unexpected ')' - no matching '(' found" }

top_level_definition:
  | DEFP   name=val_intro 
           input=val_intro 
    EQUALS body=statement DELIMITER     { Ast.Surface.defp name input body }
  | DEFC   coname=val_intro 
           input=val_intro 
    EQUALS body=statement DELIMITER     { Ast.Surface.defc coname input body }

(* Nested statements *)
statement:
  | LETP v=val_intro 
    RTLARROW p=either IN m=statement    { Ast.Surface.cut
                                            p
                                            (Ast.Surface.Negative (Ast.Surface.Consumer.mutilde v m))
                                        }
  | LETC cv=val_intro 
    RTLARROW c=either IN m=statement    { Ast.Surface.cut
                                            (Ast.Surface.Positive (Ast.Surface.Producer.mu cv m))
                                            c
                                        }
  | SPLIT    a=val_intro 
             b=val_intro        
    RTLARROW p=either IN m=statement    { Ast.Surface.cut
                                            p
                                            (Ast.Surface.Negative (Ast.Surface.Consumer.split a b m))
                                        }
  | COSPLIT  a=val_intro 
             b=val_intro       
    RTLARROW c=either IN m=statement    { Ast.Surface.cut
                                            (Ast.Surface.Positive (Ast.Surface.Producer.cosplit a b m))
                                            c
                                        }
  | cut                                 { $1 }

cut_body:
  | p=either c=either                   { Ast.Surface.cut p c }
  | either error                        { raisef $startpos($1) $endpos($1) "incomplete cut: expected consumer after producer in [%s ...]" (Ast.Surface.Show.show_neutral $1) }

cut: 
  | LBRACK c=cut_body RBRACK            { c }
  | LBRACK cut_body error               { raisef $startpos($1) $endpos($2) "unclosed cut: expected ']' to close cut started here" }
  | LBRACK error                        { raisef $startpos($1) $endpos($1) "empty cut: expected [producer consumer] after '['" }
  | RBRACK                              { raisef $startpos($1) $endpos($1) "unmatched ']': no corresponding '[' found" }

(* a definition of a name, will target this to be typed later *)
val_intro:
  | v = IDENT                           { v }

(* either a usage of a value, or a name usage *)
either:
  | n=IDENT                             { Ast.Surface.Name n }
  | p=producer                          { Ast.Surface.Positive p }
  | c=consumer                          { Ast.Surface.Negative c }

letc_body:
  | LETC cv=val_intro 
    LTRARROW s=statement                { Ast.Surface.Producer.mu cv s }
  | LETC val_intro error                { raisef $startpos($1) $endpos($2) "incomplete letcc: expected cut after covariable '%s'" $2 }
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
  | COSPLIT  a=val_intro 
             b=val_intro 
    LTRARROW s=statement                { Ast.Surface.Producer.cosplit a b s }
  | COSPLIT val_intro 
            val_intro error             { raisef $startpos($1) $endpos($3) "incomplete cosplit: expected cut after variables" }
  | COSPLIT val_intro error             { raisef $startpos($1) $endpos($2) "incomplete cosplit: expected second variable and cut" }
  | COSPLIT error                       { raisef $startpos($1) $endpos($1) "incomplete cosplit: expected (cosplit var1 var2 cut)" }

cosplit:
  | LPAREN c=cosplit_body RPAREN        { c }
  | LPAREN cosplit_body error           { raisef $startpos($1) $endpos($2) "unclosed cosplit: expected ')' to close expression started here" }

producer:
  | letc                                { $1 }
  | product                             { $1 }
  | cosplit                             { $1 }

letp_body:
  | LETP v=val_intro 
    LTRARROW s=statement                { Ast.Surface.Consumer.mutilde v s }
  | LETP val_intro error                { raisef $startpos($1) $endpos($2) "incomplete let: expected cut after variable '%s'" $2 }
  | LETP error                          { raisef $startpos($1) $endpos($1) "incomplete let: expected variable after 'let'" }

letp:
  | LPAREN l=letp_body RPAREN           { l }
  | LPAREN letp_body error              { raisef $startpos($1) $endpos($2) "unclosed let: expected ')' to close expression started here" }

split_body:
  | SPLIT    a=val_intro 
             b=val_intro 
    LTRARROW s=statement                { Ast.Surface.Consumer.split a b s }
  | SPLIT val_intro 
          val_intro error               { raisef $startpos($1) $endpos($3) "incomplete split: expected cut after variables" }
  | SPLIT val_intro error               { raisef $startpos($1) $endpos($2) "incomplete split: expected second variable and cut" }
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
  | letp                                { $1 }
  | split                               { $1 }
  | coproduct                           { $1 }
  | error                               { raisef $startpos $endpos "syntax error: expected consumer (let, split, or copair)" }

