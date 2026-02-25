%{
  open Surface
  open Loc

  let loc_of_lexing_pos (p : Lexing.position) : Loc.position =
    let file = if p.pos_fname = "" then None else Some p.pos_fname in
    { file; line = p.pos_lnum; col = p.pos_cnum - p.pos_bol + 1 }
  ;;

  let span_of (startp : Lexing.position) (endp : Lexing.position) : Loc.span =
    { start_pos = loc_of_lexing_pos startp; end_pos = loc_of_lexing_pos endp }
  ;;

  let mk_term startp endp (it : term_node) : term = Loc.mk (span_of startp endp) it
  let mk_command startp endp (it : command_node) : command =
    Loc.mk (span_of startp endp) it
  ;;

  module Gensym : sig
    val make : string -> string
  end = struct
    let counter = ref 0
    let make prefix =
      let sym = Printf.sprintf "GENSYM%d_%s" !counter prefix in
      counter := !counter + 1;
      sym
  end

  let term_binop startp endp op l_term r_term =
    let name = Gensym.make "binop_out" in
    let out_term = mk_term startp endp (Variable (Base name)) in
    let arith_cmd = Bop { op; l_term; r_term; out_term } in
    let out_binder = { name = Var name; typ = None } in
    let cmd = mk_command startp endp (Arith arith_cmd) in
    mk_term startp endp (Mu (out_binder, cmd))

  let term_unop startp endp op in_term =
    let name = Gensym.make "unop_out" in
    let out_term = mk_term startp endp (Variable (Base name)) in
    let arith_cmd = Unop { op; in_term; out_term } in
    let out_binder = { name = Var name; typ = None } in
    let cmd = mk_command startp endp (Arith arith_cmd) in
    mk_term startp endp (Mu (out_binder, cmd))

  let infer_mode shape =
    match shape with
    | Data -> By_value
    | Codata -> By_name

  (* desugars procedures into pattern matchers *)
  let make_proc startp endp binders body =
    mk_term startp endp (Matcher [
      (Tup binders, body)
    ])
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
%token SEMICOLON

%token OPEN MODULE USE AS

(* definitions *)
%token LET IN
%token REC
%token PROC
%token DO
%token DELIMITER

%token MATCH

%token TYPE
%token COLON
%token DATA CODATA
%token CBV CBN
%token PLUS MINUS NEG STAR SLASH PERCENT
%token BAR
%token ABSTRACT

(* base datatypes, along with tuples and the rest *)
%token RAW64 UNIT
%token <int64> NUMBER

%token DOT
%token COMMA

%token EXIT
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

(* -- names -- *)
binder:
  | typed_binder                                        { $1 }
  | untyped_binder                                      { $1 }

typed_binder:
  | typed_binder_aux                                    { $1 }
  | LPAREN typed_binder_aux RPAREN                      { $2 }

typed_binder_aux: 
  | name=untyped_binder COLON ty=type_use               { { name with typ = Some ty } }

untyped_binder: 
  | name=IDENT                                          { { name = Var name; typ = None } }
  | UNDERSCORE                                          { { name = Wildcard; typ = None } }

kind_binder:
  | name=IDENT
      { (name, []) }
  | name=IDENT LANGLE ts=separated_list(COMMA, CONSTRUCTOR_IDENT) RANGLE
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

maybe_delimited(item):
  | item DELIMITER?                                     { $1 }

program:
  | defs=list(maybe_delimited(top_level_item(top_level_definition)))
    maybe_command = top_level_command?
    { defs, maybe_command }

top_level_command:
  | DO statement                                        { $2 }

interface:
  | defs=list(maybe_delimited(top_level_item(top_level_signature_definition)))
    { defs }

top_level_item(definition):
  | open_statement                                      { Open $1 }
  | definition                                          { Def $1 }

open_statement:
  | OPEN n=namespaced(any_ident)      { Open n }
  | USE mod_name=namespaced(any_ident) AS use_name=any_ident
      { Use { mod_name; use_name } }

top_level_definition:
  | module_definition                                   { $1 }
  | term_definition                                     { $1 }
  | type_definition                                     { $1 }

top_level_signature_definition:
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
  | s=shape m=mode n=kind_binder EQUALS t=full_raw_type { TypeDef (n, Raw (m, s, t)) }
  | s=shape n=kind_binder EQUALS t=full_raw_type        { TypeDef (n, Raw (infer_mode s, s, t)) }
  | TYPE n=kind_binder EQUALS t=type_expr               { TypeDef (n, t) }


module_signature:
  | MODULE name=any_ident LBRACE interface=interface RBRACE
      { ModuleSigDef { name; interface  } }

term_signature:
  | LET b=untyped_binder EQUALS t=type_use              { TermSigDef (b, t) }

type_signature:
  | s=shape m=mode n=kind_binder EQUALS t=full_raw_type { TypeSigDef (n, s, Some (Raw (m, s, t))) }
  | s=shape n=kind_binder EQUALS t=full_raw_type        { TypeSigDef (n, s, Some (Raw (infer_mode s, s, t))) }
  // | s=shape n=kind_binder                               { TypeSigDef (n, s, None) }

let_definition:
  | LET b=typed_binder EQUALS t=def_term                { TermDef (b, t) }
  | LET REC b=typed_binder EQUALS t=def_term            { TermDef (b, mk_term $startpos $endpos (Rec (b, t))) }

(* procedures are sugar over matchers,
 * they are useful enough to be granted
 * native representation *)
proc_definition:
  | PROC b=untyped_binder params=proc_binders body=proc_body
      { TermDef (b, make_proc $startpos $endpos params body) }
  | PROC REC b=untyped_binder params=proc_binders body=proc_body
      {
        let proc = make_proc $startpos $endpos params body in
        TermDef (b, mk_term $startpos $endpos (Rec (b, proc)))
      }

proc_binders:
  | LPAREN separated_list(COMMA, typed_binder) RPAREN   { $2 }

proc_body:
  | LBRACE statement RBRACE                             { $2 }

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
      { mk_command $startpos $endpos (Fork (l_cmd, r_cmd)) }

(* sugared commands *)
cutlet:
  | MATCH l_term=indirect_term r_term=match_body
      { mk_command $startpos $endpos (Core { l_term; r_term }) }
  | LET b=binder RTLARROW l_term=term IN s=statement
      {
        let r_term = mk_term $startpos $endpos (Mu (b, s)) in
        mk_command $startpos $endpos (Core { l_term; r_term })
      }
  (* let rec... itself sugar over fixpoint terms *)
  | LET REC b=binder RTLARROW t=term IN s=statement
      {
        let l_term = mk_term $startpos $endpos (Rec (b, t)) in
        let r_term = mk_term $startpos $endpos (Mu (b, s)) in
        mk_command $startpos $endpos (Core { l_term; r_term })
      }
  (* ignored statement *)
  | ignored_term=term SEMICOLON rest=statement
      { let ignored_binder = { name = Wildcard; typ = None } in
        let r_term = mk_term $startpos $endpos (Mu (ignored_binder, rest)) in
        mk_command $startpos $endpos (Core { l_term = ignored_term; r_term }) 
      }

(* core commands and arithmetic operations *)
command:
  | l_term=term DOT r_term=term
      { mk_command $startpos $endpos (Core { l_term; r_term }) }
  | arith_command
      { mk_command $startpos $endpos (Arith $1) }

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

def_term:
  | indirect_term                                       { $1 }
  | naked_mu_term                                       { $1 }

indirect_term:
  | namespaced(IDENT)                                   { mk_term $startpos $endpos (Variable $1) }
  | MATCH match_body                                    { $2 }
  | product_term                                        { $1 }
  | cons_term                                           { $1 }
  | simple_number_term                                  { $1 }
  | array_term                                          { $1 }
  | EXIT                                                { mk_term $startpos $endpos Exit }
  | t=indirect_term COLON ty=type_use                   { mk_term $startpos $endpos (Ann (t, ty)) }
(*| MU naked_mu_term                                    { $2 }*)
  | LPAREN t=term RPAREN                                { t }

array_term:
  | LBRACK r_terms=separated_list(COMMA, term) RBRACK   { mk_term $startpos $endpos (Arr r_terms) }

naked_mu_term:
  | LBRACE b=binder LTRARROW t=statement RBRACE         { mk_term $startpos $endpos (Mu (b, t)) }

product_term:
  | LPAREN RPAREN
    { mk_term $startpos $endpos (Tuple []) }
  | LPAREN t=term COMMA RPAREN
    { mk_term $startpos $endpos (Tuple [t]) }
  | LPAREN t=term COMMA ts=separated_nonempty_list(COMMA, term) RPAREN
    { mk_term $startpos $endpos (Tuple (t :: ts)) }

(* direct numbers *)
simple_number_term:
  | NUMBER                                              { mk_term $startpos $endpos (Num $1) }

(* computations of numbers. these are syntactic sugar for
 * commands of numbers. For example,
 * 1 + 1 => { k -> +(1, 1 | k) } *)
active_number_term:
  | op=unop t=term %prec UNARY                          { term_unop $startpos $endpos op t }
  | l=term op=bop r=term                                { term_binop $startpos $endpos op l r }

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
  | LBRACE BAR? matches=separated_nonempty_list(BAR?, match_case) RBRACE
      { mk_term $startpos $endpos (Matcher matches) }

match_case:
  | p=pattern LTRARROW t=statement                      { (p, t) }

pattern:
  | binder
      { Binder $1 }
  | tuple_pattern
      { $1 }
  | pat_name=namespaced(CONSTRUCTOR_IDENT)
      { Constr { pat_name; pat_args = [] } }
  | pat_name=namespaced(CONSTRUCTOR_LPAREN) pat_args=separated_nonempty_list(COMMA, binder) RPAREN
      { Constr { pat_name; pat_args } }
  | NUMBER
      { Numeral $1 }

tuple_pattern:
  | LPAREN RPAREN
      { Tup [] }
  | LPAREN p=binder COMMA RPAREN
      { Tup [p] }
  | LPAREN p=binder COMMA ps=separated_nonempty_list(COMMA, binder) RPAREN
      { Tup (p :: ps) }
    (* sugar: we don't need the parentheses if we have at least two components, since the comma is unambiguous *)
  | p=binder COMMA ps=separated_nonempty_list(COMMA, binder) 
      { Tup (p :: ps) }

cons_term:
  | cons_name=namespaced(CONSTRUCTOR_IDENT)
      { mk_term $startpos $endpos (Construction { cons_name; cons_args = [] }) }
  | cons_name=namespaced(CONSTRUCTOR_LPAREN) cons_args=separated_nonempty_list(COMMA, term) RPAREN
      { mk_term $startpos $endpos (Construction { cons_name; cons_args }) }

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
  | unify_type                                          { $1 }

unify_type:
  | unify_type_aux                                      { $1 }
  (* sugar - only here to make the abstract type obvious *)
  | ABSTRACT unify_type_aux                             { $2 }

unify_type_aux:
  | LBRACK names=separated_nonempty_list(COMMA, abstract_binder) RBRACK 
    t=type_use
      { AbstractIntroducer (names, t) }

abstract_type:
  | name=abstract_binder                                { (name, false) }
  | NEG t=abstract_type                                 { let (name, negated) = t in (name, not negated) }

polarised_type:
  | p=polarity t=type_expr                              { Polarised (p, t) }
  (* sugar: unannotated is expression by default *)
  | t=type_expr                                         { Polarised (Plus, t) }

type_expr:
  | named_type                                          { $1 }
  | shaped_type                                         { $1 }
  | LPAREN type_expr RPAREN                             { $2 }

shaped_type:
  | shape=shape mode=mode raw=simple_raw_type           { Raw (mode, shape, raw) }
  (* sugar: no mode annotation means inference by shape *)
  | shape=shape raw=simple_raw_type                     { Raw (infer_mode shape, shape, raw) }

mode:
  | LBRACK CBV RBRACK                                   { By_value }
  | LBRACK CBN RBRACK                                   { By_name }

named_type:
  | n=namespaced(IDENT)
      { Named (n, []) }
  | n=namespaced(IDENT) LANGLE ts=separated_list(COMMA, type_use) RANGLE
      { Named (n, ts) }

simple_raw_type:
  | RAW64                                               { Raw64 }
  | tuple_type                                          { $1 }
  | array_type                                          { $1 }

full_raw_type:
  | variant_raw_type                                    { $1 }
  | simple_raw_type                                     { $1 }
  (*
  | RAW8                                                { type_raw8 }
  *)

variant_raw_type:
  | BAR? variants=separated_nonempty_list(BAR, variant) { Variant variants }

variant:
  | constr_name=CONSTRUCTOR_IDENT
      { { constr_name; constr_args = [] } }
  | constr_name=CONSTRUCTOR_LPAREN 
    constr_args=separated_nonempty_list(COMMA, type_use)
                RPAREN
      { { constr_name; constr_args } }

tuple_type:
  | UNIT
      { Product [] }
  | LPAREN RPAREN
      { Product [] }
  | LPAREN t=type_use COMMA RPAREN
      { Product [t] }
  | LPAREN t=type_use COMMA ts=separated_nonempty_list(COMMA, type_use) RPAREN
      { Product (t :: ts) }

array_type:
  | LBRACK t=type_use RBRACK                            { Array t }
