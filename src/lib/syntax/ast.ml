include Surface

type core_ann = { loc : Loc.span option }

let empty_core_ann : core_ann = { loc = None }

(*
 * An inferred weak type variable.
 * If it is ever compared against a more specific type, it adopts the meet of
 * the two types.
 *)
type meta_core_constraints =
  { constructor : bool option
  ; polarity : polarity option
  ; left_focusing : bool option
  ; raw_lower_bound : raw_ty option
  }

and meta_core_cell =
  | Inferred of meta_core_constraints
  | Unified of ty_use

and meta_var =
  { id : int
  ; mutable cell : meta_core_cell (* a meta var's state can be upgraded bit by bit *)
  }

and ty_use =
  | Polarised of polarity * ty
  | AbstractIntroducer of unify_ty * ty_use
  | Abstract of
      { negated : bool
      ; name : string
      ; left_focusing : bool option
      }
  (* for type inference *)
  | Weak of { mutable link : weak_cell }

and weak_cell =
  { negated : bool
  ; meta : meta_var
  }

and ty =
  | Named of name * ty_use list
  | Raw of mode * shape * raw_ty

and raw_ty =
  | Int
  | Bool
  | Product of ty_use list
  | Array of ty_use
  | Variant of variant list (* ADT *)

and variant =
  { constr_name : string
  ; constr_args : ty_use list
  }

type 'ann binder =
  | Var of 'ann * string
  | Wildcard of 'ann

type 'ann pattern =
  | Binder of 'ann binder
  | Tup of 'ann binder list
  | Constr of
      { pat_name : name
      ; pat_args : 'ann binder list
      }
  | Numeral of int64
  | Boolean of bool

type 'ann term = 'ann * 'ann term_node

and 'ann term_node =
  | Mu of 'ann binder * 'ann command (* mu and mu tilde *)
  | Variable of name
  | Construction of
      { cons_name : name
      ; cons_args : 'ann term list
      }
  | Tuple of 'ann term list
  | Matcher of ('ann pattern * 'ann command) list (* match and dispatch *)
  | Num of int64
  | Bool of bool
  | Rec of 'ann binder * 'ann term (* fixpoint term *)
  | Arr of 'ann term list
  | Ann of 'ann term * ty_use
  | Exit

and 'ann command = 'ann * 'ann command_node

and 'ann command_node =
  | Core of
      { l_term : 'ann term
      ; r_term : 'ann term
      }
  | Arith of 'ann arith_command
  | Fork of 'ann command * 'ann command

and 'ann arith_command =
  | Unop of
      { op : unop
      ; in_term : 'ann term
      ; out_term : 'ann term
      }
  | Bop of
      { op : bop
      ; l_term : 'ann term
      ; r_term : 'ann term
      ; out_term : 'ann term
      }

type 'ann mod_tli =
  | TermDef of 'ann binder * 'ann term
  | TypeDef of string * string list * ty
  (* | ModuleDef of 'ann module_def *)
  | Term of 'ann term

(* and 'ann module_def =
  { name : string
  ; program : 'ann module_
  } *)
and 'ann module_ = 'ann mod_tli top_level_item list

type sig_module = sig_tli top_level_item list

and sig_tli =
  | TypeSigDef of string * string list * shape * ty option
  | TermSigDef of core_ann binder * ty_use
(* | ModuleSigDef of module_sig_def *)

(* and module_sig_def =
  { name : string
  ; interface : sig_module
  } *)
