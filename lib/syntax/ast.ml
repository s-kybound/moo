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
  | Polarised of polarity * moded_ty
  | Abstract of
      { negated : bool
      ; name : string
      }
  (* this is for the typechecking phase, and will not be
   * created directly here *)
  | Unresolved of raw_ty

and moded_ty = mode option * ty

and ty =
  | Named of name * ty_use list
  | Raw of shape * raw_ty

and raw_ty =
  | Raw64
  | Product of ty_use list
  | Array of ty_use
  | Variant of variant list (* ADT *)
  | Destructor of raw_ty

and variant =
  { constr_name : string
  ; constr_args : ty_use list
  }

type kind_binder = string * string list

type binder =
  { name : string
  ; typ : ty_use option
  }

(* TODO: not good design *)
type pattern_binder =
  | Wildcard
  | Var of binder

type pattern =
  | Pat_binder of pattern_binder
  (* TODO: nested pattern matching for the future!
  papers:
  - "Compiling Pattern Matching to Good Decision Trees" by Luc Maranget
  - "Optimizing Pattern Matching" by Fabrice Le Fessant, Luc Maranget
  the most important thing is to find an efficient way to handle the switch-case-exit semantics
  using the duality of our calculus.
  | Tup of pattern list
  | Constr of
      { pat_name : name
      ; pat_args : pattern list
      } *)
  | Tup of pattern_binder list
  | Constr of
      { pat_name : name
      ; pat_args : pattern_binder list
      }

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

type module_open =
  | Open of name
  | Use of
      { mod_name : name
      ; use_name : string
      }

type definition =
  | TermDef of binder * term
  | TypeDef of kind_binder * ty
  | ModuleDef of module_def

and module_def =
  { name : string
  ; program : module_
  }

and module_ =
  { opens : module_open list
  ; definitions : definition list
  ; command : command option
  }

type sig_module =
  { opens : module_open list
  ; signatures : sig_definition list
  }

and sig_definition =
  | TypeSigDef of kind_binder * shape * ty option
  | TermSigDef of binder * ty_use
  | ModuleSigDef of module_sig_def

and module_sig_def =
  { name : string
  ; interface : sig_module
  }
