%{
  open Ast.Surface
  open Parser_error.Parser
%}

%token <string> IDENT
%token <string> CONSTRUCTOR_IDENT
%token UNDERSCORE

%token LBRACK RBRACK LPAREN RPAREN 
%token LBRACE RBRACE LANGLE RANGLE
%token LTRARROW RTLARROW
%token EQUALS

%token DOUBLECOLON

(* definitions *)
%token LET IN
%token REC AND
%token PROC
%token DELIMITER

%token MATCH

%token TYPE
%token COLON
%token DATA CODATA
%token CBV CBN
%token PLUS MINUS NEG
%token BAR

(* base datatypes, along with tuples and the rest *)
%token RAW8 RAW64
%token <int> NUMBER

%token DOT
%token COMMA

%token DONE 
%token EOF
%start <t> entrypoint
%%

entrypoint: p=program                   { p }

program: 
  | definitions=list_of(top_level_definition, DELIMITER?) 
    EOF                                 { program
                                          definitions
                                          (cut 
                                            (Name "no_main")
                                            (Name "'halt"))
                                        }

top_level_definition:
  | term_definition                     { $1 }
  | signature_definition                { $1 }
  | type_definition                     { $1 }

term_definition:
  | LET REC b=binder 
    EQUALS t=term                       { term_definition_rec b t }
  | LET b=binder 
    EQUALS t=term                       { term_definition b t }
  | PROC b=proc_binder
    LPAREN ps=list_of(binder, COMMA) 
    RPAREN
    LBRACE s=statement 
    RBRACE                              { proc_definition b ps s }
    
signature_definition:
  | LET b=binder 
    COLON t=polarised_type              { signature_definition b t }

list_of(elem, joiner):
  |                                     { [] }
  | elem                                { [$1] }
  | xs=list_of(elem, joiner) 
    joiner x=elem                       { xs @ [x] } 

statement:
  | cutlet                              { $1 }
  | command                             { $1 }
  | LPAREN s=statement RPAREN           { $2 }

cutlet:
  | MATCH t=term match_body             { }
  | LET b=binder 
    RTLARROW t=term 
    IN s=statement                      { }

command:
  | p=term c=term                       { command p c }

binder:
  | typed_name                          { $1 }
  | untyped_name                        { $1 }

typed_name:
  | n=untyped_name COLON t=type_use  { n }

either_ident:
  | n=IDENT                             { n }
  | c=CONSTRUCTOR_IDENT                 { c }

untyped_name:
  | n=IDENT                             { n }
  | namespace=either_ident DOUBLECOLON 
    n=untyped_name                    { Namespaced_name (namespace, n) } 

term:
  | var_term                            { $1 }
  | mu_term                             { $1 }
  | match_term                          { $1 }
  | cons_term                           { $1 }
  | tuple_term                          { $1 }
  | DONE                                { term_done }
  | LPAREN t=term RPAREN                { $2 }

var_term:
  | n=untyped_name                      { term_var n }

mu_term:
  | LBRACE b=binder 
    LTRARROW t=statement 
    RBRACE                              { term_mu b t }

match_term:
  | MATCH b=match_body                  { b }

match_body:
  | LBRACE
    matches=list_of(match_case, DELIMITER?)
    RBRACE                              { term_match matches }

match_case:
  | p=pattern 
    LTRARROW t=statement                { (p, t) }

pattern:
  | binder                              { pattern_var $1 }
(* TODO: allow matching on constant values *)
  | UNDERSCORE                          { pattern_wildcard }
  | LPAREN ps=list_of(pattern, COMMA) 
    RPAREN                              { pattern_tuple ps }
  | CONSTRUCTOR_IDENT                   { pattern_cons ($1, []) }
  | c=CONSTRUCTOR_IDENT 
    LPAREN ps=list_of(pattern, COMMA) 
    RPAREN                              { pattern_cons (c, ps) }

cons_term:
  | c=CONSTRUCTOR_IDENT                 { term_cons (c, []) }
  | c=CONSTRUCTOR_IDENT 
    LPAREN ts=list_of(term, COMMA) 
    RPAREN                              { term_cons (c, ts) }

tuple_term:
  | LPAREN ts=list_of(term, COMMA) 
    RPAREN                              { term_tuple ts }

(* TYPES *)

type_definition:
  | DATA n=type_shape EQUALS base_type  {}
  | CODATA n=type_shape EQUALS base_type{}
  | TYPE n=type_shape EQUALS type_expr  {}

type_use:
  | polarised_type              { $1 }
  | abstract_type              { $1 }

abstract_type:
  | n=abstract_name                     { type_abstract n } 
  | NEG t=abstract_type                 { type_neg t }

abstract_name:
  | CONSTRUCTOR_IDENT                   { $1 }

polar_type:
  | PLUS t=type_expr                    { polar_type_plus t }
  | t=type_expr                         { polar_type_plus t } (* sugar: unannotated is expression
                                                               * by default *)
  | MINUS t=type_expr                   { polar_type_minus t }

type_expr:
  | named_type_use                      { $1 }
  | data_type(base_type)                { $1 }
  | codata_type(base_type)              { $1 }
  | LPAREN t=type_expr RPAREN           { $2 }

named_type_use:
  | n=type_name                         { type_named n }
  | n=type_name 
    LANGLE ts=list_of(type_use, COMMA) 
    RANGLE                              { type_app (n, ts) }

type_name:
  | untyped_name                        { $1 }

data_type(t: base_type):
  | DATA t=base_type                    { type_data t }
  | cbv_annotation DATA t=base_type     { type_data_cbv (t) }
  | cbn_annotation DATA t=base_type     { type_data_cbn (t) }

codata_type(t: base_type):
  | CODATA t=base_type                  { type_codata t }
  | cbv_annotation CODATA t=base_type   { type_codata_cbv (t) }
  | cbn_annotation CODATA t=base_type   { type_codata_cbn (t) }

cbv_annotation:
  | LBRACK CBV RBRACK                  { () }

cbn_annotation:
  | LBRACK CBN RBRACK                  { () }

base_type:
  | BAR? list_of(enum_form, BAR){ type_sum $2 }
  | tuple_type                          { $1 }
  | array_type                          { $1 }
  | RAW64                               { type_raw64 }
  | RAW8                                { type_raw8 }

enum_form:
  | n=CONSTRUCTOR_IDENT                 { type_enum_case (n, []) }
  | n=CONSTRUCTOR_IDENT 
    LPAREN ts=list_of(type_use, COMMA) 
    RPAREN                              { type_enum_case_params (n, ts) }

tuple_type:
  | LPAREN ts=list_of(type_use, COMMA)
    RPAREN                              { type_tuple ts }

array_type:
  | LBRACK t=type_use DELIMITER NUMBER
    RBRACK                              { type_array t }
