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
        (match List.nth_opt kind_params i with
         | None -> Abstract (Var i)
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
    (* check if this correct *)
    | Forall (i, body) -> Forall (i, substitute_type_use body)
    | Exists (i, body) -> Exists (i, substitute_type_use body)
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
      | Forall (i, body) -> Forall (i, simplify_type_use env body)
      | Exists (i, body) -> Exists (i, simplify_type_use env body)
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

module SystemF : TYPECHECKER = struct
  (* a reference for binders. *)
  type type_env = type_use list
  (* TODO: a top level environment *)

  let rec type_use_equivalent t1 t2 =
    match t1, t2 with
    | Abstract a1, Abstract a2 ->
      let rec simplify_abstract t =
        match t with
        | Var i -> Var i
        | Neg (Var i) -> Neg (Var i)
        | Neg (Neg t') -> simplify_abstract t'
      in
      (match simplify_abstract a1, simplify_abstract a2 with
       | Var i1, Var i2 -> i1 = i2
       | Neg i1, Neg i2 -> type_use_equivalent (Abstract i1) (Abstract i2)
       | _ -> false)
    | Instantiated p1, Instantiated p2 ->
      (match p1, p2 with
       | Plus t1, Plus t2 | Minus t1, Minus t2 -> type_equivalent t1 t2
       | _ -> false)
    | _ -> false

  and type_equivalent (t1 : Core.Type.type_expr) (t2 : Core.Type.type_expr) : bool =
    match t1, t2 with
    | Name n1, Name n2 -> n1 = n2
    | PosProd ts1, PosProd ts2 | NegProd ts1, NegProd ts2 ->
      List.length ts1 = List.length ts2
      && List.for_all2 (fun a b -> type_use_equivalent a b) ts1 ts2
    | KindInstantiation (t1, args1), KindInstantiation (t2, args2) ->
      t1 = t2
      && List.length args1 = List.length args2
      && List.for_all2 (fun a b -> type_use_equivalent a b) args1 args2
    | Forall (_i1, _body1), Forall (_i2, _body2)
    | Exists (_i1, _body1), Exists (_i2, _body2) ->
      (* replace i2 with i1 in body2, then compare type_use *)
      failwith "Not implemented"
    | _ -> false
  ;;

  let invert typ =
    match typ with
    | Instantiated (Plus t) -> Instantiated (Minus t)
    | Instantiated (Minus t) -> Instantiated (Plus t)
    | Abstract (Neg a) -> Abstract a
    | Abstract a -> Abstract (Neg a)

  let rec typecheck_producer (typ_env : type_env) (p : Core.producer) : Core.Type.type_use =
    match p with
    | Mu (cut, Some typ) -> 
      (* if the typ is instantiated, ensure that it is positive *)
      begin match typ with
      | Instantiated (Minus _) -> failwith "Producer cannot have negative type"
      | _ -> typecheck_cut (typ :: typ_env) cut; invert typ
      end
    | Mu (_, None) -> failwith "System F requires type annotations on mu"
    | Tuple [] -> Instantiated (Plus (PosProd []))
    | Tuple xs -> Instantiated (Plus (PosProd (List.map (typecheck_neutral typ_env) xs)))
    | Cosplit (cut, typs) -> 
      let typs' = List.map (fun t -> match t with Some typ -> typ | None -> failwith "Type annotation required in cosplit") typs in
      typecheck_cut (typs' @ typ_env) cut; Instantiated (Plus (NegProd typs'))
    | Codone -> Instantiated (Plus (NegProd []))
    | Gen (_at, _p) -> failwith "Not implemented"
    | Pack (_at, _p) -> failwith "Not implemented"

  and typecheck_consumer (typ_env : type_env) (c : Core.consumer) : Core.Type.type_use =
    match c with
    | MuTilde (cut, Some typ) -> 
      (* if the typ is instantiated, ensure that it is negative *)
      begin match typ with
      | Instantiated (Plus _) -> failwith "Consumer cannot have positive type"
      | _ -> typecheck_cut (typ :: typ_env) cut; invert typ
      end
    | MuTilde (_, None) -> failwith "System F requires type annotations on mu-tilde"
    | Cotuple [] -> Instantiated (Minus (NegProd []))
    | Cotuple xs ->
      Instantiated (Minus (NegProd (List.map (typecheck_neutral typ_env) xs)))
    | Split (cut, typs) -> 
      let typs' = List.map (fun t -> match t with Some typ -> typ | None -> failwith "Type annotation required in split") typs in
      typecheck_cut (typs' @ typ_env) cut; Instantiated (Minus (PosProd typs'))
    | Done -> Instantiated (Minus (PosProd []))
    | Inst (_at, _c) -> failwith "Not implemented"
    | Unpack (_at, _c) -> failwith "Not implemented"

  and typecheck_neutral (typ_env : type_env) (n : Core.neutral) : Core.Type.type_use =
    match n with
    | Name (Core.Free _) -> assert false
    | Name (Core.Bound (i, Some typ)) -> begin
      match List.nth_opt typ_env i with
      | None -> failwith "Bound variable index out of range"
      | Some bound_typ -> type_use_equivalent bound_typ typ |> ignore; typ
    end
    | Name (Core.Bound (_, None)) -> failwith "Unannotated bound names are not supported in System F"
    | Positive p -> typecheck_producer typ_env p
    | Negative c -> typecheck_consumer typ_env c

  and typecheck_cut (typ_env : type_env) (cut : Core.cut) : unit =
    let p_type = typecheck_neutral typ_env cut.p in
    let c_type = typecheck_neutral typ_env cut.c in
    (* check that p_type and c_type are duals *)
    match p_type, c_type with
    | Instantiated (Plus p_base), Instantiated (Minus c_base)
    | Instantiated (Minus p_base), Instantiated (Plus c_base) ->
      if not (type_equivalent p_base c_base) then failwith "Type mismatch in cut"
    | Instantiated _, Instantiated _ -> failwith "Type mismatch in cut"
    | Abstract p_base, Abstract c_base ->
      let rec get_index_polarity base : int * bool =
        match base with
        | Var i -> i, true
        | Neg a ->
          let i, polarity = get_index_polarity a in
          i, not polarity
      in
      let p_index, p_polarity = get_index_polarity p_base in
      let c_index, c_polarity = get_index_polarity c_base in
      if p_index <> c_index || p_polarity = c_polarity
      then failwith "Type mismatch in cut"
    | _ -> failwith "Type mismatch in cut"
  ;;

  let typecheck (ast : Core.t) (env : Env.t) = 
    

  ;;
end
