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

type form =
  | Var of name
  | Wildcard
  | Tuple of form list
  | Constr of
      { form_name : name
      ; form_args : form list
      }

type term =
  | Mu of name * command
  | Variable of name
  | Construction of
      { cons_name : name
      ; cons_args : term list
      }
  | Tuple of term list
  | Matcher of (form * command) list
  | Num of int64
  | Rec of name * term (* todo - recursive terms have yet to be figured out *)
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
      { op : string
      ; in_focus_term : term
      ; out_unfocus_term : term
      }
  | Bop of
      { op : string
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

type environment_frame =
  { parent : environment_frame option
  ; bindings : (name * value) list (* todo *)
  }

type value =
  | VMu of name * control * stash * environment_frame
  | VConstruction of name * value list
  | VTuple of value list
  | VArr of value array
  | VMatcher of (form * command) list * environment_frame
  | VNum of int64
  | Done
