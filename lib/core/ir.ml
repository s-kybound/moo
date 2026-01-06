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

type name = string 

(* NON-NESTED patterns for pattern matching *)
type form =
  | Binder of name
  | Tuple of name list
  | Constr of
      { form_name : name
      ; form_args : name list
      }

type term =
  | NeedsForce of term
    (* injected during core AST conversion, will
     * instruct the runtime to force evaluation of
     * the specified term *)
  | Mu of name * command
  | Variable of name
  | Construction of
      { cons_name : name
      ; cons_args : term list
      }
  | Tuple of term list
  | Matcher of (form * command) list
  | Num of int64
  | Rec of string * term (* todo - recursive terms have yet to be figured out *)
  | Arr of term list
  | Done

and command =
  | Core of
      { focus_term : term
      ; unfocus_term : term
      }
  | Arith of arith_command
  | Fork of command * command

and arith_command =
  | Unop of
      { op : unop
      ; in_focus_term : term
      ; out_unfocus_term : term
      }
  | Bop of
      { op : bop
      ; l_focus_term : term
      ; r_focus_term : term
      ; out_unfocus_term : term
      }

type instruction =
  | Force
  | Cut
  | Spawn of command
  | Unop_instr of unop
  | Bop_instr of bop
  | Con_instr of name * int
  | Tup_instr of int
  | Arr_instr of int

type control_item =
  | I of instruction
  | T of term
  | C of command

type control = control_item list

type stash = value list

and environment_frame =
  { parent : environment_frame option
  ; mutable bindings : (string * value) list (* todo *)
  }

and value =
  | VMu of name * control * stash * environment_frame
  | VConstruction of name * value list
  | VTuple of value list
  | VArr of value array
  | VMatcher of (form * command) list * environment_frame
  | VNum of int64
  | VDone

let empty_environment : environment_frame =
  { parent = None; bindings = [] }
