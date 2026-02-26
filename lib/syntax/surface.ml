type unop =
  | Neg
  | Not

type bop =
  | Add
  | Sub
  | Mul
  | Div
  | Mod
  | And
  | Or
  | Xor
  | Shl
  | Shr

type name =
  | Base of string
  | Namespaced of
      { namespace : string
      ; inner : name
      }

type polarity =
  | Plus
  | Minus

type mode =
  | By_value
  | By_name

type shape =
  | Data
  | Codata

type ty_use =
  | Polarised of polarity * ty
  | AbstractIntroducer of string list * ty_use
  | Abstract of
      { negated : bool
      ; name : string
      }

and ty =
  | Named of name * ty_use list
  | Raw of mode * shape * raw_ty

and raw_ty =
  | Raw64
  | Product of ty_use list
  | Array of ty_use
  | Variant of variant list (* ADT *)

and variant =
  { constr_name : string
  ; constr_args : ty_use list
  }

type kind_binder = string * string list

type binder_name =
  | Var of string
  | Wildcard

type binder =
  { name : binder_name
  ; typ : ty_use option
  }

type pattern =
  | Binder of binder
  (* TODO: nested pattern matching for the future!
    papers:
    - "Compiling Pattern Matching to Good Decision Trees" by Luc Maranget
    - "Optimizing Pattern Matching" by Fabrice Le Fessant, Luc Maranget
    the most important thing is to find an efficient way to handle the switch-case-exit semantics
    using the duality of our calculus.
  *)
  | Tup of binder list
  | Constr of
      { pat_name : name
      ; pat_args : binder list
      }
  | Numeral of int64

type term = term_node Loc.located

and term_node =
  | Mu of binder * command (* mu and mu tilde *)
  | Variable of name
  | Construction of
      { cons_name : name
      ; cons_args : term list
      }
  | Tuple of term list
  | Matcher of (pattern * command) list (* match and dispatch *)
  | Num of int64
  | Rec of binder * term (* fixpoint term *)
  | Arr of term list
  | Ann of term * ty_use
  | Exit

and command = command_node Loc.located

and command_node =
  | Core of
      { l_term : term
      ; r_term : term
      }
  | Arith of arith_command
  | Fork of command * command

and arith_command =
  | Unop of
      { op : unop
      ; in_term : term
      ; out_term : term
      }
  | Bop of
      { op : bop
      ; l_term : term
      ; r_term : term
      ; out_term : term
      }

type module_open =
  | Open of name
  | Use of
      { mod_name : name
      ; use_name : string
      }

type mod_tli =
  | TermDef of binder * term
  | TypeDef of kind_binder * ty
  (* | ModuleDef of module_def *)
  | Term of term

(* and module_def =
  { name : string
  ; program : module_
  } *)
and 'a top_level_item =
  | Open of module_open
  | Def of 'a

and module_ = mod_tli top_level_item list

type sig_module = sig_tli top_level_item list

and sig_tli =
  | TypeSigDef of kind_binder * shape * ty option
  | TermSigDef of binder * ty_use
(* | ModuleSigDef of module_sig_def *)

(* and module_sig_def =
  { name : string
  ; interface : sig_module
  } *)
