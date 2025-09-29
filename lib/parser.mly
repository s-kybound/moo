%{
  open Ast.Surface
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
%token UNIT DO (* unit producer and its do consumer *)
%token COUNIT CODO (* counit consumer and its codo producer *)
%token LTRARROW RTLARROW IN (* statement syntax *)
%token DEFC DEFP (* top-level definitions *)
%token EQUALS DELIMITER (* top-level definitions *)
%token COLON (* type binder annotation *)
%token AMPERSAND STAR PLUS MINUS NEG (* type operations: negative/positive products,
                                      * positive/negative polarity,
                                      * polarity negation *)
%token TYPE (* type definition *)
%token EOF
%start <t> entrypoint
%%

entrypoint: p=program                   { p }

program: 
  | definitions=top_level_definition* 
    main=statement EOF                  { program definitions main }
  | definitions=top_level_definition* 
    EOF                                 { program
                                          definitions
                                          (cut 
                                            (Name "no_main")
                                            (Name "'halt"))
                                        }
  | LPAREN error                        { raisef $startpos($1) $endpos($1) "unexpected '(' - missing closing ')' or malformed expression" }
  | RPAREN error                        { raisef $startpos($1) $endpos($1) "unexpected ')' - no matching '(' found" }

producer_definition:
  | DEFP   name=var_intro 
           input=var_intro 
    EQUALS body=statement DELIMITER?    { defp name input body }

consumer_definition:
  | DEFC   coname=var_intro 
           input=var_intro 
    EQUALS body=statement DELIMITER?    { defc coname input body }

top_level_definition:
  | producer_definition                 { $1 }
  | consumer_definition                 { $1 }
  | type_definition                     { $1 }

(* Nested statements *)
statement:
  | LETP v=var_intro 
    RTLARROW p=either IN m=statement    { cut
                                            p
                                            (Negative (Consumer.mutilde v m))
                                        }
  | LETC cv=var_intro 
    RTLARROW c=either IN m=statement    { cut
                                            (Positive (Producer.mu cv m))
                                            c
                                        }
  | SPLIT    a=var_intro 
             b=var_intro        
    RTLARROW p=either IN m=statement    { cut
                                            p
                                            (Negative (Consumer.split a b m))
                                        }
  | COSPLIT  a=var_intro 
             b=var_intro       
    RTLARROW c=either IN m=statement    { cut
                                            (Positive (Producer.cosplit a b m))
                                            c
                                        }
  | DO RTLARROW p=either 
    IN m=statement                      { cut
                                            p
                                            (Negative (Consumer.do_ m))
                                        }
  | CODO RTLARROW c=either 
    IN m=statement                      { cut
                                            (Positive (Producer.codo m))
                                            c
                                        }
  | cut                                 { $1 }

cut_body:
  | p=either c=either                   { cut p c }
  | either error                        { raisef $startpos($1) $endpos($1) "incomplete cut: expected consumer after producer in [%s ...]" (Show.show_neutral $1) }

cut: 
  | LBRACK c=cut_body RBRACK            { c }
  | LBRACK cut_body error               { raisef $startpos($1) $endpos($2) "unclosed cut: expected ']' to close cut started here" }
  | LBRACK error                        { raisef $startpos($1) $endpos($1) "empty cut: expected [producer consumer] after '['" }
  | RBRACK                              { raisef $startpos($1) $endpos($1) "unmatched ']': no corresponding '[' found" }

var_intro:
  | typed_var                           { $1 }
  | untyped_var                         { $1 }

tyvar:
  | IDENT                               { $1 }

type_schema:
  | v=tyvar                             { Type.Base v } (* basic type * *)
  | LPAREN name=tyvar abs=tyvar+ RPAREN { Type.Kind (name, abs) } (* a kind * -> * *)

abstract_type:
  | v=tyvar                             { Type.Var v }
  | NEG v=abstract_type                 { 
                                          require_adjacent $endpos($1) $startpos(v) "'~' must immediately precede the type (no spaces)";
                                          (* this will flip the negation of the nested abstract type *)
                                          match v with
                                          | Type.Var _ -> Type.Neg v
                                          | Type.Neg v -> v
                                        }

(* usage of a type, only allowed within 
 * the body of another polar type *)
type_use:
  | p=polar_type                        { Type.Instantiated p }
  | a=abstract_type                     { Type.Abstract a }

type_invocation_body:
  | kind=tyvar vars=type_use+           { Type.KindInstantiation (kind, vars) }
  | tyvar error                         { raisef $startpos($1) $endpos($1) "we do not allow nullary kinds, that's what the base kinds is for!" }

positive_product_body:
  | STAR a=type_use b=type_use          { Type.PosProd (a, b) }
  | STAR type_use type_use error        { raisef $startpos($1) $endpos($1) "* expects ONLY two types!" }
  | STAR type_use error                 { raisef $startpos($1) $endpos($1) "* expects two types! please supply another type" }

negative_product_body:
  | AMPERSAND a=type_use b=type_use     { Type.NegProd (a, b) }
  | AMPERSAND type_use type_use error   { raisef $startpos($1) $endpos($1) "& expects ONLY two types!" }
  | AMPERSAND type_use error            { raisef $startpos($1) $endpos($1) "& expects two types! please supply another type" }

(* base_types, only used in definitions. 
 * should be unpolarized. *)
base_type:
  | v=tyvar                             { Type.Name v }
  | LPAREN 
    app=type_invocation_body  
    RPAREN                              { app }
  | LPAREN 
    pprod=positive_product_body 
    RPAREN                              { pprod }
  | LPAREN 
    nprod=negative_product_body
    RPAREN                              { nprod }

polar_type:
  | b=base_type PLUS                    { 
                                          require_adjacent $endpos(b) $startpos($2) "'+' must immediately follow the type (no spaces)"; 
                                          Type.Plus b
                                        }
  | b=base_type MINUS                   { 
                                          require_adjacent $endpos(b) $startpos($2) "'-' must immediately follow the type (no spaces)"; 
                                          Type.Minus b
                                        }

typed_var_body:
  | v=IDENT COLON t=type_use            { make_name v (Some t) }

type_definition:
  | TYPE shape=type_schema
    EQUALS expr=base_type
    DELIMITER?                          { TypeDef (shape, expr) }

typed_var:
  | LBRACK t=typed_var_body RBRACK      { t }

untyped_var:
  | v=IDENT                             { make_name v None }

(* either a usage of a value, or a name usage *)
either:
  | n=IDENT                             { Name n }
  | p=producer                          { Positive p }
  | c=consumer                          { Negative c }

letc_body:
  | LETC cv=var_intro 
    LTRARROW s=statement                { Producer.mu cv s }
  | LETC cv=var_intro error             { raisef $startpos($1) $endpos(cv) "incomplete letcc: expected cut after covariable '%s'" cv.name }
  | LETC error                          { raisef $startpos($1) $endpos($1) "incomplete letcc: expected covariable after 'letcc'" }

letc:
  | LPAREN l=letc_body RPAREN           { l }
  | LPAREN letc_body error              { raisef $startpos($1) $endpos($2) "unclosed letcc: expected ')' to close expression started here" }

product_body:
  | PAIR a=either b=either              { Producer.pair a b }
  | PAIR either error                   { raisef $startpos($1) $endpos($2) "incomplete pair: expected second element after first element" } 
  | PAIR error                          { raisef $startpos($1) $endpos($1) "incomplete pair: expected two elements like (pair x y)" } 

product:
  | LPAREN p=product_body RPAREN        { p }
  | LPAREN product_body error           { raisef $startpos($1) $endpos($2) "unclosed pair: expected ')' to close pair started here" }

cosplit_body:
  | COSPLIT  a=var_intro 
             b=var_intro 
    LTRARROW s=statement                { Producer.cosplit a b s }
  | COSPLIT var_intro 
            var_intro error             { raisef $startpos($1) $endpos($3) "incomplete cosplit: expected cut after variables" }
  | COSPLIT var_intro error             { raisef $startpos($1) $endpos($2) "incomplete cosplit: expected second variable and cut" }
  | COSPLIT error                       { raisef $startpos($1) $endpos($1) "incomplete cosplit: expected (cosplit var1 var2 cut)" }

cosplit:
  | LPAREN c=cosplit_body RPAREN        { c }
  | LPAREN cosplit_body error           { raisef $startpos($1) $endpos($2) "unclosed cosplit: expected ')' to close expression started here" }

unit:
  | UNIT                                { Unit }

codo_body:
  | CODO LTRARROW s=statement           { Producer.codo s }

codo:
  | LPAREN c=codo_body RPAREN           { c }
  | LPAREN codo_body error              { raisef $startpos($1) $endpos($2) "unclosed codo: expected ')' to close expression started here" }

producer:
  | letc                                { $1 }
  | product                             { $1 }
  | cosplit                             { $1 }
  | unit                                { $1 }
  | codo                                { $1 }

letp_body:
  | LETP v=var_intro 
    LTRARROW s=statement                { Consumer.mutilde v s }
  | LETP v=var_intro error              { raisef $startpos($1) $endpos(v) "incomplete let: expected cut after variable '%s'" v.name }
  | LETP error                          { raisef $startpos($1) $endpos($1) "incomplete let: expected variable after 'let'" }

letp:
  | LPAREN l=letp_body RPAREN           { l }
  | LPAREN letp_body error              { raisef $startpos($1) $endpos($2) "unclosed let: expected ')' to close expression started here" }

split_body:
  | SPLIT    a=var_intro 
             b=var_intro 
    LTRARROW s=statement                { Consumer.split a b s }
  | SPLIT var_intro 
          var_intro error               { raisef $startpos($1) $endpos($3) "incomplete split: expected cut after variables" }
  | SPLIT var_intro error               { raisef $startpos($1) $endpos($2) "incomplete split: expected second variable and cut" }
  | SPLIT error                         { raisef $startpos($1) $endpos($1) "incomplete split: expected (split var1 var2 cut)" }

split:
  | LPAREN s=split_body RPAREN          { s }
  | LPAREN split_body error             { raisef $startpos($1) $endpos($2) "unclosed split: expected ')' to close expression started here" }

coproduct_body:
  | COPAIR a=either b=either            { Consumer.copair a b }
  | COPAIR either error                 { raisef $startpos($1) $endpos($2) "incomplete copair: expected second element after first element" } 
  | COPAIR error                        { raisef $startpos($1) $endpos($1) "incomplete copair: expected two elements like (copair x y)" } 

coproduct:
  | LPAREN c=coproduct_body RPAREN      { c }
  | LPAREN coproduct_body error         { raisef $startpos($1) $endpos($2) "unclosed copair: expected ')' to close expression started here" }

counit:
  | COUNIT                              { Counit }

do_body:
  | DO LTRARROW s=statement             { Consumer.do_ s }

do_:
  | LPAREN d=do_body RPAREN             { d }
  | LPAREN do_body error                { raisef $startpos($1) $endpos($2) "unclosed do: expected ')' to close expression started here" }

consumer: 
  | letp                                { $1 }
  | split                               { $1 }
  | coproduct                           { $1 }
  | counit                              { $1 }
  | do_                                 { $1 }

