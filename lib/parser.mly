%{  
  open Parser_error.Parser
  let require_adjacent prev_end curr_start error_msg =
    if prev_end.Lexing.pos_cnum < curr_start.Lexing.pos_cnum then
      raisef curr_start curr_start error_msg
    else
      ()
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
%token AMPERSAND STAR PLUS MINUS NEG (* type operations: negative/positive products,
                                      * positive/negative polarity,
                                      * polarity negation *)
%token TYPE (* type definition *)
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

producer_definition:
  | DEFP   name=var_intro 
           input=var_intro 
    EQUALS body=statement DELIMITER?    { Ast.Surface.defp name input body }

consumer_definition:
  | DEFC   coname=var_intro 
           input=var_intro 
    EQUALS body=statement DELIMITER?    { Ast.Surface.defc coname input body }

top_level_definition:
  | producer_definition                 { $1 }
  | consumer_definition                 { $1 }
  | type_definition                     { $1 }

(* Nested statements *)
statement:
  | LETP v=var_intro 
    RTLARROW p=either IN m=statement    { Ast.Surface.cut
                                            p
                                            (Ast.Surface.Negative (Ast.Surface.Consumer.mutilde v m))
                                        }
  | LETC cv=var_intro 
    RTLARROW c=either IN m=statement    { Ast.Surface.cut
                                            (Ast.Surface.Positive (Ast.Surface.Producer.mu cv m))
                                            c
                                        }
  | SPLIT    a=var_intro 
             b=var_intro        
    RTLARROW p=either IN m=statement    { Ast.Surface.cut
                                            p
                                            (Ast.Surface.Negative (Ast.Surface.Consumer.split a b m))
                                        }
  | COSPLIT  a=var_intro 
             b=var_intro       
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

var_intro:
  | typed_var                           { $1 }
  | untyped_var                         { $1 }

type_shape:
  | tyvar                               { } (* basic type * *)
  | LPAREN tyvar tyvar+ RPAREN          { } (* a kind * -> * *)

tyvar:
  | IDENT                               { }

abstract_type:
  | tyvar                               { }
  | NEG tyvar                           { require_adjacent $endpos($1) $startpos($2) "'~' must immediately precede the type (no spaces)" }

(* usage of a type, only allowed within 
 * the body of another polar type *)
type_use:
  | polar_type(type_use)                { }
  | abstract_type                       { }

type_use_strict:
  | polar_type(type_use_strict)         { }
  | abstract_type error                 { raisef $startpos($1) $endpos($1) "abstract type is not allowed in a strict context (most likely this type is being used to type a term)" }

type_invocation_body(use_rule):
  | tyvar use_rule+                     { }
  | tyvar error                         { raisef $startpos($1) $endpos($1) "we do not allow nullary kinds, that's what the base kinds is for!" }

positive_product_body(use_rule):
  | STAR use_rule use_rule              { }
  | STAR use_rule use_rule error        { raisef $startpos($1) $endpos($1) "* expects ONLY two types!" }
  | STAR use_rule error                 { raisef $startpos($1) $endpos($1) "* expects two types! please supply another type" }

negative_product_body(use_rule):
  | AMPERSAND use_rule use_rule         { }
  | AMPERSAND use_rule use_rule error   { raisef $startpos($1) $endpos($1) "& expects ONLY two types!" }
  | AMPERSAND use_rule error            { raisef $startpos($1) $endpos($1) "& expects two types! please supply another type" }

(* base_types, only used in definitions. 
 * should be unpolarized. *)
base_type(use_rule):
  | tyvar                               { }
  | LPAREN 
    type_invocation_body(use_rule)  
    RPAREN                              { }
  | LPAREN 
    positive_product_body(use_rule) 
    RPAREN                              { }
  | LPAREN 
    negative_product_body(use_rule) 
    RPAREN                              { }

polar_type(use_rule):
  | base_type(use_rule) PLUS            { require_adjacent $endpos($1) $startpos($2) "'+' must immediately follow the type (no spaces)" }
  | base_type(use_rule) MINUS           { require_adjacent $endpos($1) $startpos($2) "'-' must immediately follow the type (no spaces)" }

typed_var_body:
  | v=IDENT COLON type_use_strict       { v }

type_definition:
  | TYPE _shape=type_shape
    EQUALS _expr=base_type(type_use) 
    DELIMITER?                          { Ast.Surface.Type }

typed_var:
  | LBRACK t=typed_var_body RBRACK      { t }

untyped_var:
  | IDENT                               { raisef $startpos($1) $endpos($1) "welcome to the simply typed product mu mu-tilde calculus! please type this with [%s : <type>]." $1 }

(* either a usage of a value, or a name usage *)
either:
  | n=IDENT                             { Ast.Surface.Name n }
  | p=producer                          { Ast.Surface.Positive p }
  | c=consumer                          { Ast.Surface.Negative c }

letc_body:
  | LETC cv=var_intro 
    LTRARROW s=statement                { Ast.Surface.Producer.mu cv s }
  | LETC var_intro error                { raisef $startpos($1) $endpos($2) "incomplete letcc: expected cut after covariable '%s'" $2 }
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
  | COSPLIT  a=var_intro 
             b=var_intro 
    LTRARROW s=statement                { Ast.Surface.Producer.cosplit a b s }
  | COSPLIT var_intro 
            var_intro error             { raisef $startpos($1) $endpos($3) "incomplete cosplit: expected cut after variables" }
  | COSPLIT var_intro error             { raisef $startpos($1) $endpos($2) "incomplete cosplit: expected second variable and cut" }
  | COSPLIT error                       { raisef $startpos($1) $endpos($1) "incomplete cosplit: expected (cosplit var1 var2 cut)" }

cosplit:
  | LPAREN c=cosplit_body RPAREN        { c }
  | LPAREN cosplit_body error           { raisef $startpos($1) $endpos($2) "unclosed cosplit: expected ')' to close expression started here" }

producer:
  | letc                                { $1 }
  | product                             { $1 }
  | cosplit                             { $1 }

letp_body:
  | LETP v=var_intro 
    LTRARROW s=statement                { Ast.Surface.Consumer.mutilde v s }
  | LETP var_intro error                { raisef $startpos($1) $endpos($2) "incomplete let: expected cut after variable '%s'" $2 }
  | LETP error                          { raisef $startpos($1) $endpos($1) "incomplete let: expected variable after 'let'" }

letp:
  | LPAREN l=letp_body RPAREN           { l }
  | LPAREN letp_body error              { raisef $startpos($1) $endpos($2) "unclosed let: expected ')' to close expression started here" }

split_body:
  | SPLIT    a=var_intro 
             b=var_intro 
    LTRARROW s=statement                { Ast.Surface.Consumer.split a b s }
  | SPLIT var_intro 
          var_intro error               { raisef $startpos($1) $endpos($3) "incomplete split: expected cut after variables" }
  | SPLIT var_intro error               { raisef $startpos($1) $endpos($2) "incomplete split: expected second variable and cut" }
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

