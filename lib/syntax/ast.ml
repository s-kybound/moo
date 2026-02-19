include Surface

(* from shape, one can discover polarity *)
type unresolved_tyu_state =
  { mode : mode option ref
  ; shape : shape option ref
  }

and ty_use =
  | Polarised of polarity * ty
  | Abstract of
      { negated : bool
      ; name : string
      }
  (* for type inference *)
  | Constructor of unresolved_tyu_state * raw_ty
  | Destructor of unresolved_tyu_state * raw_ty

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

type binder =
  | Var of string
  | Wildcard

type pattern =
  | Binder of binder
  | Tup of binder list
  | Constr of
      { pat_name : name
      ; pat_args : binder list
      }
  | Numeral of int64

type term =
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
  | Done

and command =
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

type definition =
  | TermDef of binder * term
  | TypeDef of kind_binder * ty
  | ModuleDef of module_def

and module_def =
  { name : string
  ; program : module_
  }

and module_ = definition top_level_item list * command option

type sig_module = sig_definition top_level_item list

and sig_definition =
  | TypeSigDef of kind_binder * shape * ty option
  | TermSigDef of binder * ty_use
  | ModuleSigDef of module_sig_def

and module_sig_def =
  { name : string
  ; interface : sig_module
  }
