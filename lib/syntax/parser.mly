%{
  open Ast

  module Gensym : sig
    val make : string -> string
  end = struct
    let counter = ref 0
    let make prefix =
      let sym = Printf.sprintf "GENSYM%d_%s" !counter prefix in
      counter := !counter + 1;
      sym
  end

  let term_binop op l_term r_term =
    let name = Gensym.make "binop_out" in
    let arith_cmd = Bop { op; l_term; r_term; out_term = Variable (Base name) } in
    let out_binder = { name; typ = None } in
    Mu (out_binder, Arith arith_cmd)

  let term_unop op in_term =
    let name = Gensym.make "unop_out" in
    let arith_cmd = Unop { op; in_term; out_term = Variable (Base name) } in
    let out_binder = { name; typ = None } in
    Mu (out_binder, Arith arith_cmd)

  (* constructs a moded type.
   * infers mode if necessary *)
  let make_moded_type mode_opt ty =
    match mode_opt, ty with
    (* can't infer without shape info *)
    | _, Named _ -> mode_opt, ty
    | Some _, Raw _ -> mode_opt, ty
    (* default inferences *)
    | None, Raw (Data, _) -> Some By_value, ty
    | None, Raw (Codata, _) -> Some By_name, ty

  (* desugars procedures into pattern matchers *)
  let make_proc binders body =
    Matcher [
      (Tup (List.map (fun b -> Var b) binders), body)
    ]
%}

%token <string> IDENT
%token <string> NAMESPACE_IDENT
%token <string> CONSTRUCTOR_IDENT
%token <string> CONSTRUCTOR_LPAREN
%token UNDERSCORE

%token LBRACK RBRACK LPAREN RPAREN
%token LBRACE RBRACE LANGLE RANGLE
%token LTRARROW RTLARROW
%token EQUALS

%token OPEN MODULE USE AS

(* definitions *)
%token LET IN
%token REC
%token PROC
%token DEF
%token DELIMITER

%token MATCH

%token TYPE
%token COLON
%token DATA CODATA
%token CBV CBN
%token PLUS MINUS NEG STAR SLASH PERCENT
%token BAR

(* base datatypes, along with tuples and the rest *)
%token RAW64 UNIT
%token <int64> NUMBER

%token DOT
%token COMMA

%token DONE
%token EOF

(* token associativities and precedences *)
(*%left AMPERSAND BAR
%left CARET
%left LANGLE RANGLE *)
%left PLUS MINUS
%left STAR SLASH PERCENT
%right UNARY

%start <module_> parse_program
%start <sig_module> parse_signature
%%
(* -- auxillary helpers -- *)
list_of(elem, joiner):
  |                                                     { [] }
  | nonempty_list_of(elem, joiner)                      { $1 }

nonempty_list_of(elem, joiner):
  | x=elem xs=nonempty_list_of_2(elem, joiner)          { x :: xs }

nonempty_list_of_2(elem, joiner):
  |                                                     { [] }
  | joiner xs=nonempty_list_of(elem, joiner)            { xs }

(* -- names -- *)
binder:
  | typed_binder                                        { $1 }
  | untyped_binder                                      { $1 }

typed_binder: name=untyped_binder COLON ty=type_use     { { name with typ = Some ty } }

untyped_binder: name=IDENT                              { { name; typ = None } }

kind_binder:
  | name=IDENT
      { (name, []) }
  | name=IDENT LANGLE ts=list_of(CONSTRUCTOR_IDENT, COMMA) RANGLE
      { (name, ts) }

%inline abstract_binder:
  | CONSTRUCTOR_IDENT                                   { $1 }

any_ident:
  | IDENT                                               { $1 }
  | CONSTRUCTOR_IDENT                                   { $1 }

namespaced(name):
  | name                                                { Base $1 }
  | namespace=NAMESPACE_IDENT
    inner=namespaced(name)                              { Namespaced {namespace; inner} }

(* -- PROGRAM STRUCTURE -- *)
parse_program: program EOF                              { $1 }

parse_signature: interface EOF                          { $1 }

program:
  | opens=list_of(open_statement, DELIMITER?) 
    definitions=list_of(top_level_definition, DELIMITER?)
    maybe_command = statement?
      { { opens; definitions; command = maybe_command } }

interface:
  | opens=list_of(open_statement, DELIMITER?) 
    signatures=list_of(top_level_signature, DELIMITER?)
      { { opens; signatures } }

open_statement:
  | OPEN n=namespaced(any_ident)
      { Open n }
  | USE mod_name=namespaced(any_ident) AS use_name=any_ident    
      { Use { mod_name; use_name } }

top_level_definition:
  | module_definition                                   { $1 }
  | term_definition                                     { $1 }
  | type_definition                                     { $1 }

top_level_signature:
  | module_signature                                    { $1 }
  | term_signature                                      { $1 }
  | type_signature                                      { $1 }

module_definition:
  | MODULE name=any_ident LBRACE program=program RBRACE
      { ModuleDef { name; program } }

term_definition:
  | let_definition                                      { $1 }
  | proc_definition                                     { $1 }

type_definition:
  | s=shape n=kind_binder EQUALS t=full_raw_type        { TypeDef (n, Raw (s, t)) }
  | TYPE n=kind_binder EQUALS t=type_expr               { TypeDef (n, t) }


module_signature:
  | MODULE name=any_ident LBRACE interface=interface RBRACE
      { ModuleSigDef { name; interface  } }

term_signature:
  | DEF b=binder EQUALS t=type_use                      { TermSigDef (b, t) }

(* type signatures should expose whether
 * the type is data or codata.
 * this will allow developers to still know the
 * default evaluation strategy for any type. *)
type_signature:
  | s=shape n=kind_binder EQUALS t=full_raw_type        { TypeSigDef (n, s, Some (Raw (s, t))) }
  | s=shape n=kind_binder                               { TypeSigDef (n, s, None) }

let_definition:
  | DEF b=binder EQUALS t=term                          { TermDef (b, t) }
  | DEF REC b=binder EQUALS t=term                      { TermDef (b, Rec (b, t)) }

(* procedures are sugar over matchers,
 * they are useful enough to be granted
 * native representation *)
proc_definition:
  | PROC b=untyped_binder params=proc_binders body=proc_body
      { TermDef (b, make_proc params body) }
  | PROC REC b=untyped_binder params=proc_binders body=proc_body
      { TermDef (b, Rec (b, make_proc params body)) }

proc_binders:
  | LPAREN list_of(binder, COMMA) RPAREN                { $2 }

proc_body:
  | LBRACE statement RBRACE                           { $2 }

(* -- STATEMENTS AND TERMS -- *)

(* any form of command *)
statement:
  | non_fork_statement                                  { $1 }
  | fork_command                                        { $1 }

non_fork_statement:
  | cutlet                                              { $1 }
  | command                                             { $1 }
  | LPAREN s=statement RPAREN                           { s }

(* execute two commands concurrently
 * for now, we are limiting the power of fork
 * and preventing it from directly spawning
 * > 2 commands at a time *)
fork_command:
  | LBRACK l_cmd=non_fork_statement BAR r_cmd=non_fork_statement RBRACK
      { Fork (l_cmd, r_cmd) }

(* sugared commands *)
cutlet:
  | MATCH l_term=indirect_term r_term=match_body        { Core { l_term; r_term } }
  | LET b=binder RTLARROW l_term=term IN s=statement    { let r_term = Mu (b, s) in Core { l_term; r_term } }
  (* let rec... itself sugar over fixpoint terms *)
  | LET REC b=binder RTLARROW t=term IN s=statement     { let l_term = Rec (b, t) in
                                                          let r_term = Mu (b, s) in
                                                          Core { l_term; r_term }
                                                        }

(* core commands and arithmetic operations *)
command:
  | l_term=term DOT r_term=term                         { Core { l_term; r_term } }
  | arith_command                                       { Arith $1 }

(* base operations over numeric data types.
 * may be extended in the future to support other
 * base types *)
arith_command:
  | op=unop LPAREN in_term=term BAR out_term=term RPAREN
      { Unop { op; in_term; out_term } }
  | op=bop LPAREN l_term=term COMMA r_term=term BAR out_term=term RPAREN
      { Bop { op; l_term; r_term; out_term } }

(* indirect terms are terms that are not
 * syntactically direct mu bindings.
 * this is needed to avoid a grammar ambiguity *)
term:
  | naked_mu_term                                       { $1 }
  | active_number_term                                  { $1 }
  | indirect_term                                       { $1 }

indirect_term:
  | namespaced(IDENT)                                   { Variable $1 }
  | MATCH match_body                                    { $2 }
  | product_term                                        { $1 }
  | cons_term                                           { $1 }
  | simple_number_term                                  { $1 }
  | array_term                                          { $1 }
  | DONE                                                { Done }
  | t=indirect_term COLON ty=type_use                   { Ann (t, ty) }
(*| MU naked_mu_term                                    { $2 }*)
  | LPAREN t=term RPAREN                                { t }

array_term:
  | LBRACK r_terms=list_of(term, COMMA) RBRACK          { Arr r_terms }

naked_mu_term:
  | LBRACE b=binder LTRARROW t=statement RBRACE         { Mu (b, t) }

product_term:
  | LPAREN RPAREN
      { Tuple [] }
  | LPAREN t=term COMMA RPAREN
      { Tuple [t] }
  | LPAREN t=term COMMA ts=nonempty_list_of(term, COMMA) RPAREN
      { Tuple (t :: ts) }

(* direct numbers *)
simple_number_term:
  | NUMBER                                              { Num $1 }

(* computations of numbers. these are syntactic sugar for
 * commands of numbers. For example,
 * 1 + 1 => { k -> +(1, 1 | k) } *)
active_number_term:
  | op=unop t=term %prec UNARY                          { term_unop op t }
  | l=term op=bop r=term                                { term_binop op l r }

%inline unop:
  | MINUS                                               { Neg }
  | NEG                                                 { Not }

%inline bop:
  | PLUS                                                { Add }
  | MINUS                                               { Sub }
  | STAR                                                { Mul }
  | SLASH                                               { Div }
  | PERCENT                                             { Mod }
  (*
  | AMPERSAND AMPERSAND                                 { And }
  | BAR BAR                                             { Or }
  | CARET                                               { Xor }
  | LANGLE LANGLE                                       { Shl }
  | RANGLE RANGLE                                       { Shr }
  *)

match_body:
  | LBRACE BAR? matches=nonempty_list_of(match_case, BAR?) RBRACE
      { Matcher matches }

match_case:
  | p=pattern LTRARROW t=statement                      { (p, t) }

pattern:
  | binder
      { Var $1 }
  | UNDERSCORE
      { Wildcard }
  | tuple_pattern
      { $1 }
  | pat_name=namespaced(CONSTRUCTOR_IDENT)
      { Constr { pat_name; pat_args = [] } }
  | pat_name=namespaced(CONSTRUCTOR_LPAREN) pat_args=nonempty_list_of(pattern, COMMA) RPAREN
      { Constr { pat_name; pat_args } }
  (* TODO: allow matching on constant values *)

tuple_pattern:
  | LPAREN RPAREN
      { Tup [] }
  | LPAREN p=pattern COMMA RPAREN
      { Tup [p] }
  | LPAREN p=pattern COMMA ps=nonempty_list_of(pattern, COMMA) RPAREN
      { Tup (p :: ps) }

cons_term:
  | cons_name=namespaced(CONSTRUCTOR_IDENT)
      { Construction { cons_name; cons_args = [] } }
  | cons_name=namespaced(CONSTRUCTOR_LPAREN) cons_args=nonempty_list_of(term, COMMA) RPAREN
      { Construction { cons_name; cons_args } }

(* TYPES *)

polarity:
  | PLUS                                                { Plus }
  | MINUS                                               { Minus }

shape:
  | DATA                                                { Data }
  | CODATA                                              { Codata }

type_use:
  | polarised_type                                      { $1 }
  | abstract_type                                       { let (name, negated) = $1 in Abstract { name; negated } }

abstract_type:
  | name=abstract_binder                                { (name, false) }
  | NEG t=abstract_type                                 { let (name, negated) = t in (name, not negated) }

polarised_type:
  | p=polarity t=moded_type                             { Polarised (p, t) }
  (* sugar: unannotated is expression by default *)
  | t=moded_type                                        { Polarised (Plus, t) }

moded_type:
  | mode=maybe_mode t=type_expr                         { make_moded_type mode t }

type_expr:
  | named_type                                          { $1 }
  | shape=shape raw=simple_raw_type                     { Raw (shape, raw) }
  | shape=shape LBRACE raw=adt_raw_type RBRACE          { Raw (shape, raw) }

maybe_mode:
  |                                                     { None }
  | LBRACK CBV RBRACK                                   { Some By_value }
  | LBRACK CBN RBRACK                                   { Some By_name }

named_type:
  | n=namespaced(IDENT)
      { Named (n, []) }
  | n=namespaced(IDENT) LANGLE ts=list_of(type_use, COMMA) RANGLE
      { Named (n, ts) }

adt_raw_type:
  | BAR? variants=nonempty_list_of(variant, BAR)        { ADT variants }

simple_raw_type:
  | RAW64                                               { Raw64 }
  | tuple_type                                          { $1 }
  | array_type                                          { $1 }

full_raw_type:
  | adt_raw_type                                        { $1 }
  | simple_raw_type                                     { $1 }
  (*
  | RAW8                                                { type_raw8 }
  *)

variant:
  | n=CONSTRUCTOR_IDENT
      { (n, []) }
  | n=CONSTRUCTOR_LPAREN ts=nonempty_list_of(type_use, COMMA) RPAREN
      { (n, ts) }

tuple_type:
  | UNIT
      { Unit }
  | LPAREN RPAREN
      { Unit }
  | LPAREN t=type_use COMMA RPAREN
      { Product [t] }
  | LPAREN t=type_use COMMA ts=nonempty_list_of(type_use, COMMA) RPAREN
      { Product (t :: ts) }

array_type:
  | LBRACK t=type_use RBRACK                            { Array t }
