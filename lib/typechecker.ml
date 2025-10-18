open Ast
open Core.Type

exception TypeError of (string * Lexing.position) list

module TypeSubstituter = struct
  (** substitute type variables in a type expression *)
  let rec substitute_type_expr ~(kind_params : type_use list) ~(kind_body : type_expr)
    : type_expr
    =
    let rec substitute_type_use (t : type_use) : type_use =
      match t with
      | Abstract a -> substitute_abstract_type a
      | Instantiated p -> Instantiated (substitute_polar_type p)
    and substitute_polar_type (p : polar_type) : polar_type =
      match p with
      | Plus t -> Plus (substitute_type_expr ~kind_params ~kind_body:t)
      | Minus t -> Minus (substitute_type_expr ~kind_params ~kind_body:t)
    and substitute_abstract_type (a : abstract_type) : type_use =
      match a with
      | Var i ->
        (* should have been verified by now *)
        (match List.nth_opt kind_params i with
         | None -> failwith "Type variable index out of bounds"
         | Some tu -> tu)
      | Neg a ->
        (match substitute_abstract_type a with
         | Instantiated (Plus t) -> Instantiated (Minus t)
         | Instantiated (Minus t) -> Instantiated (Plus t)
         | Abstract a' -> Abstract (Neg a'))
    in
    match kind_body with
    | Name n -> Name n
    | PosProd typs -> PosProd (List.map substitute_type_use typs)
    | NegProd typs -> NegProd (List.map substitute_type_use typs)
    | KindInstantiation (t, args) ->
      let substituted_args = List.map substitute_type_use args in
      KindInstantiation (t, substituted_args)
  ;;

  let rec simplify_type_use (env : Env.t) (t : type_use) : type_use =
    let rec simplify_polar_type (p : polar_type) : polar_type =
      match p with
      | Plus t -> Plus (simplify_type_expr t)
      | Minus t -> Minus (simplify_type_expr t)
    and simplify_type_expr (t : type_expr) : type_expr =
      match t with
      | Name n ->
        (* we also need to deal with base types here
         * this is our base case *)
        (* lookup the type in the environment *)
        if Env.has_type env n
        then (
          match Env.get_type env n with
          | Error _ -> failwith ("Type " ^ n ^ " not found in environment")
          | Ok (schema, body) ->
            (match schema with
             | Base _ -> simplify_type_expr body
             | Kind _ -> failwith "Cannot instantiate kind type without arguments"))
        else failwith ("Type " ^ n ^ " not found in environment")
      | PosProd ts -> PosProd (List.map (simplify_type_use env) ts)
      | NegProd ts -> NegProd (List.map (simplify_type_use env) ts)
      | KindInstantiation (t, args) ->
        let simplified_args = List.map (simplify_type_use env) args in
        (* lookup the kind, instantiate it, and simplify *)
        (match Env.get_type env t with
         | Error _ -> failwith ("Type " ^ t ^ " not found in environment")
         | Ok (schema, kind_body) ->
           let instantiated_body =
             match schema with
             | Base _ -> failwith "Cannot instantiate base type"
             | Kind (_, params_num) ->
               if List.length simplified_args <> params_num
               then
                 failwith
                   (Printf.sprintf
                      "Kind %s expects %d parameters, but got %d"
                      t
                      params_num
                      (List.length simplified_args))
               else substitute_type_expr ~kind_params:simplified_args ~kind_body
           in
           simplify_type_expr instantiated_body)
    in
    match t with
    | Abstract a -> Abstract a (* polymorphic types, leave them alone *)
    | Instantiated p -> Instantiated (simplify_polar_type p)
  ;;
end

module type TYPECHECKER = sig
  val typecheck : Core.t -> (Core.t, exn) result
end

module Untyped : TYPECHECKER = struct
  let typecheck ast = Ok ast
end

module SimplyTyped : TYPECHECKER = struct
  let typecheck _ast = Error (Failure "simply-typed typechecker not implemented")
end

module SystemF : TYPECHECKER = struct
  let typecheck _ast = Error (Failure "system-F typechecker not implemented")
end

module HindleyMilner : TYPECHECKER = struct
  let typecheck _ast = Error (Failure "hindley-milner typechecker not implemented")
end
