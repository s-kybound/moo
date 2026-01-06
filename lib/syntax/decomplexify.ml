open Ast

let gensym _s = failwith "gensym not implemented"

let rec decomplexify_term (t : term) : term =
  match t with
  | Mu (binder, command) ->
    let new_command = decomplexify_command command in
    Mu (binder, new_command)
  | Variable _ -> t
  | Construction { cons_name; cons_args } ->
    Construction { cons_name; cons_args = List.map decomplexify_term cons_args }
  | Tuple terms -> Tuple (List.map decomplexify_term terms)
  | Matcher [] -> t
  | Matcher matches -> 
    let match_val = gensym "match_val" in
    Matcher (decomplexify_matcher [match_val] matches)
  | Num _ -> t
  | Rec (binder, body) -> Rec (binder, decomplexify_term body)
  | Arr terms -> Arr (List.map decomplexify_term terms)
  | Ann (term, ty_use) -> Ann (decomplexify_term term, ty_use)
  | Done -> t

and decomplexify_command (c : command) : command =
  match c with
  | Core { l_term; r_term } ->
    Core { l_term = decomplexify_term l_term; r_term = decomplexify_term r_term }
  | Arith (Unop { op; in_term; out_term }) ->
    Arith
      (Unop
         { op
         ; in_term = decomplexify_term in_term
         ; out_term = decomplexify_term out_term
         })
  | Arith (Bop { op; l_term; r_term; out_term }) ->
    Arith
      (Bop
         { op
         ; l_term = decomplexify_term l_term
         ; r_term = decomplexify_term r_term
         ; out_term = decomplexify_term out_term
         })
  | Fork (cmd1, cmd2) -> Fork (decomplexify_command cmd1, decomplexify_command cmd2)

(* core invariant - the original match is type-correct! 
 * this will allow us to avoid painful success and error commands 
 * inspired by paper "Optimizing Pattern Matching by Fabrice Le Fessant, Luc Maranget"
 *)
and decomplexify_matcher
      (_vars : binder list)
      (_matches : (pattern * command) list)
  : (pattern * command) list
  =
  raise (Failure "decomplexify_matcher not implemented")
  (*
  (* this considers the pattern match as a matrix of patterns *)
  let decomplexify_matcher_aux
      (vars : binder list)
      (matches : (pattern list * command) list) 
    : (pattern * command) list
  =
  match matches with
  | [] -> assert false
  | _ ->
  match vars with
  | [] -> 
*)
;;
