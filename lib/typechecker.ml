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

  let substitute_abstract_with (body : type_use) (i : int) (replacement : type_use)
    : type_use
    =
    let rec substitute_in_abstract (a : abstract_type) : type_use =
      match a with
      | Var j -> if i = j then replacement else Abstract (Var j)
      | Neg a' ->
        (match substitute_in_abstract a' with
         | Instantiated (Plus t) -> Instantiated (Minus t)
         | Instantiated (Minus t) -> Instantiated (Plus t)
         | Abstract a'' -> Abstract (Neg a''))
    and substitute_in_type_use (t : type_use) : type_use =
      match t with
      | Abstract a -> substitute_in_abstract a
      | Instantiated p -> Instantiated (substitute_in_polar_type p)
    and substitute_in_polar_type (p : polar_type) : polar_type =
      match p with
      | Plus t -> Plus (substitute_in_type_expr t)
      | Minus t -> Minus (substitute_in_type_expr t)
    and substitute_in_type_expr (t : type_expr) : type_expr =
      match t with
      | Name n -> Name n
      | PosProd typs -> PosProd (List.map substitute_in_type_use typs)
      | NegProd typs -> NegProd (List.map substitute_in_type_use typs)
      | KindInstantiation (t, args) ->
        let substituted_args = List.map substitute_in_type_use args in
        KindInstantiation (t, substituted_args)
      | Forall (j, body) -> Forall (j, substitute_in_type_use body)
      | Exists (j, body) -> Exists (j, substitute_in_type_use body)
    in
    substitute_in_type_use body
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
  (* do all the substitution before typechecking for now *)
  val typecheck : Env.t -> Core.t -> (Core.t, exn) result
end

module Untyped : TYPECHECKER = struct
  let typecheck _env ast = Ok ast
end

module SystemF : TYPECHECKER = struct
  (* a reference for abstract binders. *)
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
    | Forall (i1, body1), Forall (i2, body2) | Exists (i1, body1), Exists (i2, body2) ->
      (* replace i2 with i1 in body2, then compare type_use *)
      let body2' =
        TypeSubstituter.substitute_abstract_with body2 i2 (Abstract (Var i1))
      in
      type_use_equivalent body1 body2'
    | _ -> false
  ;;

  let invert typ =
    match typ with
    | Instantiated (Plus t) -> Instantiated (Minus t)
    | Instantiated (Minus t) -> Instantiated (Plus t)
    | Abstract (Neg a) -> Abstract a
    | Abstract a -> Abstract (Neg a)
  ;;

  let verify_type_use (typ_env : type_env) (typ : Core.Type.type_use) : Core.Type.type_use
    =
    let rec verify_abstract (a : Core.Type.abstract_type) : unit =
      match a with
      | Var i ->
        (* check if it is in typ_env*)
        if not (List.mem (Abstract a) typ_env)
        then failwith ("Unbound type variable: " ^ string_of_int i)
      | Neg a' -> verify_abstract a'
    and verify_type_use_inner (t : Core.Type.type_use) : unit =
      match t with
      | Abstract a -> verify_abstract a
      | Instantiated p -> verify_polar_type p
    and verify_polar_type (p : Core.Type.polar_type) : unit =
      match p with
      | Plus t -> verify_type_expr t
      | Minus t -> verify_type_expr t
    and verify_type_expr (t : Core.Type.type_expr) : unit =
      match t with
      | Name _ -> ()
      | PosProd typs | NegProd typs -> List.iter verify_type_use_inner typs
      | KindInstantiation (_, args) -> List.iter verify_type_use_inner args
      | Forall (_, body) | Exists (_, body) -> verify_type_use_inner body
    in
    verify_type_use_inner typ;
    typ
  ;;

  let rec typecheck_producer (typ_env : type_env) (p : Core.producer) : Core.Type.type_use
    =
    match p with
    | Mu (cut, Some typ) ->
      (* if the typ is instantiated, ensure that it is positive *)
      (match typ with
       | Instantiated (Plus _) -> failwith "Producer cannot bind positive type"
       | _ ->
         typecheck_cut (typ :: typ_env) cut;
         invert (verify_type_use typ_env typ))
    | Mu (_, None) -> failwith "System F requires type annotations on mu"
    | Tuple [] -> Instantiated (Plus (PosProd []))
    | Tuple xs -> Instantiated (Plus (PosProd (List.map (typecheck_neutral typ_env) xs)))
    | Cosplit (cut, typs) ->
      let typs' =
        List.map
          (fun t ->
            match t with
            | Some typ -> verify_type_use typ_env typ
            | None -> failwith "Type annotation required in cosplit")
          typs
      in
      typecheck_cut (typs' @ typ_env) cut;
      Instantiated (Plus (NegProd typs'))
    | Codone -> Instantiated (Plus (NegProd []))
    | Gen (at, p) ->
      let abs_type = Abstract (Var at) in
      let body_type = typecheck_neutral (abs_type :: typ_env) p in
      Instantiated (Plus (Forall (at, body_type)))
    | Pack (bt, at, p) ->
      (match bt with
       | Forall (i, body) ->
         let instantiated_body = TypeSubstituter.substitute_abstract_with body i at in
         let body_type = typecheck_neutral typ_env p in
         if not (type_use_equivalent instantiated_body body_type)
         then failwith "Type mismatch in packing"
         else Instantiated (Plus bt)
       | _ -> failwith "Cannot pack non-polymorphic type")

  and typecheck_consumer (typ_env : type_env) (c : Core.consumer) : Core.Type.type_use =
    match c with
    | MuTilde (cut, Some typ) ->
      (* if the typ is instantiated, ensure that it is negative *)
      (match typ with
       | Instantiated (Minus _) -> failwith "Consumer cannot bind negative type"
       | _ ->
         typecheck_cut (typ :: typ_env) cut;
         invert (verify_type_use typ_env typ))
    | MuTilde (_, None) -> failwith "System F requires type annotations on mu-tilde"
    | Cotuple [] -> Instantiated (Minus (NegProd []))
    | Cotuple xs ->
      Instantiated (Minus (NegProd (List.map (typecheck_neutral typ_env) xs)))
    | Split (cut, typs) ->
      let typs' =
        List.map
          (fun t ->
             match t with
             | Some typ -> verify_type_use typ_env typ
             | None -> failwith "Type annotation required in split")
          typs
      in
      typecheck_cut (typs' @ typ_env) cut;
      Instantiated (Minus (PosProd typs'))
    | Done -> Instantiated (Minus (PosProd []))
    | Inst (bt, at, c) ->
      (match bt with
       | Forall (i, body) ->
         let instantiated_body = TypeSubstituter.substitute_abstract_with body i at in
         let body_type = typecheck_neutral typ_env c in
         if not (type_use_equivalent instantiated_body body_type)
         then failwith "Type mismatch in instantiation"
         else Instantiated (Minus bt)
       | _ -> failwith "Cannot instantiate non-polymorphic type")
    | Unpack (at, c) ->
      let abs_type = Abstract (Var at) in
      let body_type = typecheck_neutral (abs_type :: typ_env) c in
      Instantiated (Minus (Exists (at, body_type)))

  and typecheck_neutral (typ_env : type_env) (n : Core.neutral) : Core.Type.type_use =
    match n with
    | Name (Core.Free _) -> failwith "No free names are allowed!"
    | Name (Core.Bound (_, Some typ)) -> verify_type_use typ_env typ
    | Name (Core.Bound (_, None)) ->
      failwith "Unannotated bound names are not supported in System F"
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

  let typecheck (_env : Env.t) (ast : Core.t) =
    try
      typecheck_cut [] ast.main;
      Ok ast
    with
    | exn -> Error exn
  ;;
end
