open Ast
open Core

(* this module is used to store the definitions of a program, including
 * terms and types. *)
type t =
  { terms : (string, neutral) Hashtbl.t
  ; types : (Type.type_schema, Type.type_expr) Hashtbl.t
  }

let empty_env () : t = { terms = Hashtbl.create 10; types = Hashtbl.create 10 }
let is_defined i (t : t) = Hashtbl.mem t.terms i

let get_neutral i (t : t) =
  match Hashtbl.find_opt t.terms i with
  | None -> failwith "not_found"
  | Some n -> n
;;

module Substituter = struct
  let rec substitute_producer env p =
    match p with
    | Mu (cut, typ) -> Mu (substitute_cut env cut, typ)
    | Pair (a, b) -> Pair (substitute_neutral env a, substitute_neutral env b)
    | Cosplit (cut, typ1, typ2) -> Cosplit (substitute_cut env cut, typ1, typ2)
    | Unit -> Unit
    | Codo cut -> Codo (substitute_cut env cut)

  and substitute_consumer env c =
    match c with
    | MuTilde (cut, typ) -> MuTilde (substitute_cut env cut, typ)
    | Split (cut, typ1, typ2) -> Split (substitute_cut env cut, typ1, typ2)
    | Copair (a, b) -> Copair (substitute_neutral env a, substitute_neutral env b)
    | Counit -> Counit
    | Do cut -> Do (substitute_cut env cut)

  and substitute_cut env cut =
    { p = substitute_neutral env cut.p; c = substitute_neutral env cut.c }

  and substitute_neutral env n =
    match n with
    | Name (Free name) when is_defined name env -> get_neutral name env
    | Name x -> Name x
    | Positive p -> Positive (substitute_producer env p)
    | Negative c -> Negative (substitute_consumer env c)
  ;;
end

let add_term t name term = Hashtbl.replace t.terms name term
let add_type t schema expr = Hashtbl.replace t.types schema expr

(* load the definitions into the environment.
   * only done after typechecking and syntax checking
   * has been done. *)
let load_definitions program t =
  List.iter
    (fun (d : definition) ->
       match d with
       (*
          no recursive names yet
         | Producer_rec (n, p) ->
         | Consumer_rec (cn, c) ->
       *)
       | Producer (n, p) ->
         let p = Substituter.substitute_producer t p in
         add_term t n (Positive p)
       | Consumer (cn, c) ->
         let c = Substituter.substitute_consumer t c in
         add_term t cn (Negative c)
       | TypeDef (schema, expr) ->
         (* there's no need to substitute other definitions within
            * the type expr, we leave that work to our typechecker. *)
         add_type t schema expr)
    program.definitions
;;

let substitute_definitions cut t = Substituter.substitute_cut t cut
