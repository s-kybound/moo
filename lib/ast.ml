(* This is the user facing AST of pluto-charon. 
 * The variables should be converted into using de Brujin indices
 * by a first pass before further execution. *)
module Surface = struct
  type name = string

  type producer = 
    | V of name
    | Mu of name * cut

  and consumer =
    | C of name
    | MuTilde of name * cut

  (* < p | c > *)
  and cut = {
    p: producer;
    c: consumer;
  }

  type t = cut

  let cut p c = { p; c }
end