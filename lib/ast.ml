(* This is the user facing AST of pluto-charon. 
 * The variables should be converted into using de Brujin indices
 * by a first pass before further execution. *)
module Surface = struct
  type producer = 
    | V of string
    | Mu of string * cut
  and consumer =
    | C of string
    | MuTilde of string * cut
  and cut = {
    p: producer;
    c: consumer;
  }

  type t = cut

  module Show = struct
    let rec show_producer p =
      match p with
      | V name -> name
      | Mu (coname, cut) -> Printf.sprintf "(μ %s .%s)" coname (show_cut cut)
    and show_consumer c =
      match c with
      | C coname -> Printf.sprintf "'%s" coname
      | MuTilde (name, cut) -> Printf.sprintf "(μ̃ %s .%s)" name (show_cut cut)
    and show_cut cut =
      Printf.sprintf "<%s|%s>" (show_producer cut.p) (show_consumer cut.c)

    let show = show_cut
  end

  let variable name = V name
  let covariable coname = C coname

  let mu coname cut = Mu (coname, cut)
  let mutilde name cut = MuTilde (name, cut)
  let cut p c = { p; c }
end

module Core = struct 
  type name = 
    | Free of string
    | Bound of int

  type producer = 
    | V of name
    | Mu of cut
  and consumer =
    | C of name
    | MuTilde of cut
  and cut = {
    p: producer;
    c: consumer;
  }

  type t = cut

  module Converter = struct
    type unprocessed_syntax = 
    | Producer of Surface.producer
    | Consumer of Surface.consumer
    | Cut of Surface.cut
  end
end