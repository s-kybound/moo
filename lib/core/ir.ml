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
  | Numeral of int64

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
  | Rec of string * term
  | Arr of term list
  | Val of value
  | Exit

and command =
  | Core of
      { focus_term : term
      ; unfocus_term : term
      }
  | Arith of arith_command
  | Fork of command * command
  | ModEndHole (* module end command *)

and arith_command =
  | Unop of
      { op : unop
      ; in_term : term
      ; out_term : term
      ; left_focus : bool
      }
  | Bop of
      { op : bop
      ; l_focus_term : term
      ; r_focus_term : term
      ; out_term : term
      ; left_focus : bool
      }

and instruction =
  | Force
  | Cut
  | Spawn of command
  | Unop_instr of unop
  | Bop_instr of bop
  | Con_instr of name * int
  | Tup_instr of int
  | Arr_instr of int
  | Set_instr of name (* sets the nearest binding to the value on the stack *)
  | Exit_env
(* exits the current environment, returning control to the parent environment *)

and control_item =
  | I of instruction
  | T of term
  | C of command

and control = control_item list
and stash = value list

and environment_frame =
  | Top
  | Frame of
      { parent : environment_frame
      ; binding : string
      ; mutable value : value
      }

and value =
  | VMu of name * control * stash * environment_frame
  | VConstruction of name * value list
  | VTuple of value list
  | VArr of value array
  | VMatcher of (form * command) list * environment_frame
  | VNum of int64
  | VExit
  | VHole
(* placeholder value for recursive terms that will be updated to the correct value once done *)

let empty_environment : environment_frame = Top

type state = control * stash * environment_frame
