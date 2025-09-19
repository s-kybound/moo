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

  and cut =
    { p : producer
    ; c : consumer
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
    ;;

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

  and cut =
    { p : producer
    ; c : consumer
    }

  type t = cut

  module Show = struct
    let show_name name =
      match name with
      | Free name -> name
      | Bound n -> string_of_int n
    ;;

    let rec show_producer p =
      match p with
      | V name -> show_name name
      | Mu cut -> Printf.sprintf "(μ.%s)" (show_cut cut)

    and show_consumer c =
      match c with
      | C coname -> Printf.sprintf "'%s" (show_name coname)
      | MuTilde cut -> Printf.sprintf "(μ̃.%s)" (show_cut cut)

    and show_cut cut =
      Printf.sprintf "<%s|%s>" (show_producer cut.p) (show_consumer cut.c)
    ;;

    let show = show_cut
  end

  module Converter = struct
    module S = Surface

    (* our environment tracks two of stacks of names and conames respectively *)
    type env =
      { names : string list
      ; conames : string list
      }

    let empty_env = { names = []; conames = [] }

    let rec lookup_aux stack n depth =
      match stack with
      | [] -> None
      | n' :: stack' ->
        if String.equal n n' then Some depth else lookup_aux stack' n (depth + 1)
    ;;

    let lookup_name env name : name =
      Option.fold (lookup_aux env.names name 0) ~none:(Free name) ~some:(fun depth ->
        Bound depth)
    ;;

    let lookup_coname env coname : name =
      Option.fold
        (lookup_aux env.conames coname 0)
        ~none:(Free coname)
        ~some:(fun depth -> Bound depth)
    ;;

    let push_name x env = { env with names = x :: env.names }
    let push_coname k env = { env with conames = k :: env.conames }

    let rec convert_producer env p : producer =
      match p with
      | S.V name -> V (lookup_name env name)
      | S.Mu (k, cut) -> Mu (convert_cut (push_coname k env) cut)

    and convert_consumer env c : consumer =
      match c with
      | S.C coname -> C (lookup_coname env coname)
      | S.MuTilde (v, cut) -> MuTilde (convert_cut (push_name v env) cut)

    and convert_cut env cut : cut =
      { p = convert_producer env cut.p; c = convert_consumer env cut.c }
    ;;
  end

  let convert : Surface.t -> t = Converter.convert_cut Converter.empty_env
end
