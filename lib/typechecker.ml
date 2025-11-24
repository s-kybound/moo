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

  let simplify_type_expr env t = 
    match simplify_type_use env (Instantiated (Plus t)) with
    | Instantiated (Plus t') -> t'
    | _ -> assert false
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
  type abstract_type_env = abstract_type list

(* ensures that all abstract type usages are well scoped (they have been introduced before) *)
  let verify_type_use (abstract_type_env : abstract_type_env) tenv (typ : Core.Type.type_use) : Core.Type.type_use
    =
    let rec subst_abstract abstract_type_env (a : Core.Type.abstract_type) : Core.Type.abstract_type =
      match a with
      | Var i ->
        (* check if it is in type_env *)
        if not (List.mem a abstract_type_env)
        then begin
          failwith ("Unbound type variable: " ^ string_of_int i) end
        else a
      | Neg a' -> Neg (subst_abstract abstract_type_env a')
    and subst_type_use_inner abstract_type_env (t : Core.Type.type_use) : Core.Type.type_use =
      match t with
      | Abstract a -> Abstract (subst_abstract abstract_type_env a)
      | Instantiated p -> Instantiated (subst_polar_type abstract_type_env p)
    and subst_polar_type abstract_type_env (p : Core.Type.polar_type) : Core.Type.polar_type =
      match p with
      | Plus t -> Plus (subst_type_expr abstract_type_env t)
      | Minus t -> Minus (subst_type_expr abstract_type_env t)
    and subst_type_expr abstract_type_env (t : Core.Type.type_expr) : Core.Type.type_expr =
      match t with
      | Name _ -> assert false (* names should have been substituted by now *) 
      | PosProd typs -> PosProd (List.map (subst_type_use_inner abstract_type_env) typs)
      | NegProd typs -> NegProd (List.map (subst_type_use_inner abstract_type_env) typs)
      | KindInstantiation _ -> assert false
      | Forall (i, body) -> Forall (i, subst_type_use_inner ((Var i)::abstract_type_env) body)
      | Exists (i, body) -> Exists (i, subst_type_use_inner ((Var i)::abstract_type_env) body)
    in
    subst_type_use_inner abstract_type_env (TypeSubstituter.simplify_type_use tenv typ)
  ;;

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

  

  let rec typecheck_producer abstract_type_env (type_env : type_env) tenv (p : Core.producer) : Core.Type.type_use
    =
    match p with
    | Mu (command, Some typ) ->
      (* if the typ is instantiated, ensure that it is positive *)
      (match typ with
       | Instantiated (Plus _) -> failwith 
       (Printf.sprintf "Type mismatch in mu-abstraction: expects negative type, got %s" (Core.Type.Show.show_type_use typ))
       | _ ->
         typecheck_cut abstract_type_env (typ :: type_env) tenv command;
         invert (verify_type_use abstract_type_env tenv typ))
    | Mu (_, None) -> failwith "System F requires type annotations on mu"
    | Tuple [] -> Instantiated (Plus (PosProd []))
    | Tuple xs -> Instantiated (Plus (PosProd (List.map (typecheck_neutral abstract_type_env type_env tenv) xs)))
    | Cosplit (command, typs) ->
      let typs' =
        List.map
          (fun t ->
            match t with
            | Some typ -> verify_type_use abstract_type_env tenv typ
            | None -> failwith "Type annotation required in cosplit")
          typs
      in
      typecheck_cut abstract_type_env(typs' @ type_env) tenv command;
      Instantiated (Plus (NegProd typs'))
    | Codone -> Instantiated (Plus (NegProd []))
    | Gen (at, p) ->
      let abs_type = Var at in
      let body_type = typecheck_neutral (abs_type :: abstract_type_env) type_env tenv p in
      Instantiated (Plus (Forall (at, body_type)))
    | Pack (bt, at, p) ->
      let bt' = TypeSubstituter.simplify_type_expr tenv bt in
      (match bt' with
       | Exists (i, body) ->
         let instantiated_body = TypeSubstituter.substitute_abstract_with body i at in
         let body_type = typecheck_neutral abstract_type_env type_env tenv p in
         if not (type_use_equivalent instantiated_body body_type)
         then failwith (Printf.sprintf "Type mismatch in pack body: expected %s but got %s"
                          (Core.Type.Show.show_type_use instantiated_body)
                          (Core.Type.Show.show_type_use body_type))
         else Instantiated (Plus bt')
       | _ -> failwith (Printf.sprintf "Type mismatch in pack: cannot pack non-existential base type %s"
                          (Core.Type.Show.show_type_expr bt')))

  and typecheck_consumer abstract_type_env (type_env : type_env) tenv (c : Core.consumer) : Core.Type.type_use =
    match c with
    | MuTilde (command, Some typ) ->
      (* if the typ is instantiated, ensure that it is negative *)
      (match typ with
       | Instantiated (Minus _) -> failwith (Printf.sprintf "Type mismatch in mu-tilde-abstraction: expects positive type, got %s" (Core.Type.Show.show_type_use typ))
       | _ ->
         typecheck_cut abstract_type_env (typ :: type_env) tenv command;
         invert (verify_type_use abstract_type_env tenv typ))
    | MuTilde (_, None) -> failwith "System F requires type annotations on mu-tilde"
    | Cotuple [] -> Instantiated (Minus (NegProd []))
    | Cotuple xs ->
      Instantiated (Minus (NegProd (List.map (typecheck_neutral abstract_type_env type_env tenv) xs)))
    | Split (command, typs) ->
      let typs' =
        List.map
          (fun t ->
             match t with
             | Some typ -> verify_type_use abstract_type_env tenv typ
             | None -> failwith "Type annotation required in split")
          typs
      in
      typecheck_cut abstract_type_env (typs' @ type_env) tenv command;
      Instantiated (Minus (PosProd typs'))
    | Done -> Instantiated (Minus (PosProd []))
    | Inst (bt, at, c) ->
      let bt' = TypeSubstituter.simplify_type_expr tenv bt in
      (match bt' with
       | Forall (i, body) ->
         let instantiated_body = TypeSubstituter.substitute_abstract_with body i at in
         let body_type = typecheck_neutral abstract_type_env type_env tenv c in
         if not (type_use_equivalent instantiated_body (invert body_type))
         then failwith (Printf.sprintf "Type mismatch in inst body: expected %s but got %s"
                          (Core.Type.Show.show_type_use instantiated_body)
                          (Core.Type.Show.show_type_use body_type))
         else Instantiated (Minus bt')
        | _ -> failwith (Printf.sprintf "Type mismatch in inst: cannot instantiate non-universal base type %s"
                           (Core.Type.Show.show_type_expr bt')))
    | Unpack (at, c) ->
      let abs_type = Var at in
      let body_type = typecheck_neutral (abs_type :: abstract_type_env) type_env tenv c in
      Instantiated (Minus (Exists (at, invert body_type)))

  and typecheck_neutral abstract_type_env (type_env : type_env) tenv (n : Core.neutral) : Core.Type.type_use =
    match n with
    | Name (Core.Free n) ->
      if not (Env.has_term tenv n)
      then failwith ("Unbound name: " ^ n)
      else
        let neutral = Env.get_neutral n tenv in
        typecheck_neutral abstract_type_env type_env tenv neutral 
    | Name (Core.Bound (i, Some typ)) -> 
      (* get the type from the type environment *)
      let typ' = 
        verify_type_use abstract_type_env tenv (List.nth type_env i)
      in
      let typ = verify_type_use abstract_type_env tenv typ in
      if not (type_use_equivalent typ typ')
      then failwith (Printf.sprintf "Type mismatch in bound name: expected %s but got %s"
                       (Core.Type.Show.show_type_use typ')
                       (Core.Type.Show.show_type_use typ))
      else verify_type_use abstract_type_env tenv typ
    | Name (Core.Bound (_, None)) ->
      failwith "Unannotated bound names are not supported in System F"
    | Positive p -> typecheck_producer abstract_type_env type_env tenv p
    | Negative c -> typecheck_consumer abstract_type_env type_env tenv c
  and typecheck_cut abstract_type_env (type_env : type_env) tenv (command : Core.cut) : unit =
    let p_type = typecheck_neutral abstract_type_env type_env tenv command.p in
    let c_type = typecheck_neutral abstract_type_env type_env tenv command.c in
    (* check that p_type and c_type are duals *)
    match p_type, c_type with
    | Instantiated (Plus p_base), Instantiated (Minus c_base)
    | Instantiated (Minus p_base), Instantiated (Plus c_base) ->
      if not (type_equivalent p_base c_base) then failwith (Printf.sprintf "Type mismatch in command: attempt to pair %s with %s"
                                                             (Core.Type.Show.show_type_expr p_base)
                                                             (Core.Type.Show.show_type_expr c_base))
    | Instantiated (Plus _), Instantiated _ -> failwith (Printf.sprintf "Type mismatch in command: both sides positive: %s vs %s"
                                                          (Core.Type.Show.show_type_use p_type)
                                                         (Core.Type.Show.show_type_use c_type))
    | Instantiated (Minus _), Instantiated _ -> failwith (Printf.sprintf "Type mismatch in command: both sides negative: %s vs %s"
                                                           (Core.Type.Show.show_type_use p_type)
                                                          (Core.Type.Show.show_type_use c_type))
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
      if p_index <> c_index
      then failwith (Printf.sprintf "Type mismatch in command: attempt to pair type variables %d and %d"
                       p_index
                       c_index)
      else if p_polarity = c_polarity
      then failwith (Printf.sprintf "Type mismatch in command: both sides have same polarity for type variable %d"
                       p_index)
    | _ -> failwith (Printf.sprintf "Type mismatch in command: cannot pair %s with %s"
                       (Core.Type.Show.show_type_use p_type)
                       (Core.Type.Show.show_type_use c_type))
  ;;

  let typecheck (env : Env.t) (ast : Core.t) =
    try
      typecheck_cut [] [] env ast.main;
      Ok ast
    with
    | exn -> Error exn
  ;;
end
