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
%token TICKLPAREN
%token COMMA (* the above are also for tuple, cotuple construction *)
%token LETC LETP (* mu, mu-tilde abstactions *)
%token SPLIT (* tuple consumer *)
%token COSPLIT (* cotuple producer *)
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

list_of(elem, joiner):
  |                                     { [] }
  | elem                                { [$1] }
  | xs=list_of(elem, joiner) 
    joiner x=elem                       { xs @ [x] } 

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
  | SPLIT    LPAREN xs=list_of(var_intro, COMMA) RPAREN    
    RTLARROW p=either IN m=statement    { cut
                                            p
                                            (Negative (Consumer.split xs m))
                                        }
  | COSPLIT  TICKLPAREN xs=list_of(var_intro, COMMA) RPAREN       
    RTLARROW c=either IN m=statement    { cut
                                            (Positive (Producer.cosplit xs m))
                                            c
                                        }
  | cut                                 { $1 }

cut_body:
  | p=either c=either                   { cut p c }

cut: 
  | LBRACK c=cut_body RBRACK            { c }

var_intro:
  | typed_var                           { $1 }
  | untyped_var                         { $1 }

tyvar:
  | IDENT                               { $1 }

type_schema:
  | v=tyvar                             { Type.Base v }           (* basic type * *)
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
  | tyvar error                         { raisef $startpos($1) $endpos($1) "we do not allow nullary kinds, that's what base kinds are for!" }

positive_product_body:
  | STAR                                { Type.PosProd [] }
  | STAR type_use                       { Type.PosProd [$2]}
  | x=type_use STAR xs=list_of(type_use, STAR)        
                                        { Type.PosProd (x::xs) }

negative_product_body:
  | AMPERSAND                           { Type.NegProd [] }
  | AMPERSAND type_use                  { Type.NegProd [$2]}
  | x=type_use AMPERSAND xs=list_of(type_use, AMPERSAND)        
                                        { Type.NegProd (x::xs) }

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
  | list_of(either, COMMA)              { Producer.tuple $1 }

product:
  | LPAREN p=product_body RPAREN        { p }
  | LPAREN product_body error           { raisef $startpos($1) $endpos($2) "unclosed tuple: expected ')' to close tuple started here" }

cosplit_body:
  | COSPLIT  TICKLPAREN xs=list_of(var_intro, COMMA) RPAREN       
    LTRARROW s=statement                { Producer.cosplit xs s }

cosplit:
  | LPAREN c=cosplit_body RPAREN        { c }
  | LPAREN cosplit_body error           { raisef $startpos($1) $endpos($2) "unclosed cosplit: expected ')' to close expression started here" }

producer:
  | letc                                { $1 }
  | product                             { $1 }
  | cosplit                             { $1 }

letp_body:
  | LETP v=var_intro 
    LTRARROW s=statement                { Consumer.mutilde v s }
  | LETP v=var_intro error              { raisef $startpos($1) $endpos(v) "incomplete let: expected cut after variable '%s'" v.name }
  | LETP error                          { raisef $startpos($1) $endpos($1) "incomplete let: expected variable after 'let'" }

letp:
  | LPAREN l=letp_body RPAREN           { l }
  | LPAREN letp_body error              { raisef $startpos($1) $endpos($2) "unclosed let: expected ')' to close expression started here" }

split_body:
  | SPLIT    LPAREN xs=list_of(var_intro, COMMA) RPAREN    
    LTRARROW s=statement                { Consumer.split xs s }

split:
  | LPAREN s=split_body RPAREN          { s }
  | LPAREN split_body error             { raisef $startpos($1) $endpos($2) "unclosed split: expected ')' to close expression started here" }

coproduct_body:
  | list_of(either, COMMA)              { Consumer.cotuple $1 }

coproduct:
  | TICKLPAREN c=coproduct_body RPAREN  { c }
  | TICKLPAREN coproduct_body error     { raisef $startpos($1) $endpos($2) "unclosed cotuple: expected ')' to close expression started here" }

consumer: 
  | letp                                { $1 }
  | split                               { $1 }
  | coproduct                           { $1 }

