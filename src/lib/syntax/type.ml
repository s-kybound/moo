open Utils.Fresh
open Ast

exception MalformedType of name * string
exception TypeNotFound of name
exception TypeInstantiationFailure of name * int * int

(* name -> abstracts * type *)
type tydef_env = (string list * ty) Env.t

(* name -> type_use *)
type ty_env = Ast.ty_use Env.t

let qualify_name (origin_path : string list) (name : name) : name =
  match origin_path, name with
  | [], _ | _, Namespaced _ -> name
  | _, Base base_name -> Namespaced (origin_path, base_name)
;;

let rec qualify_tyu (origin_path : string list) (ty_use : ty_use) : ty_use =
  match ty_use with
  | Polarised (polarity, ty) -> Polarised (polarity, qualify_ty origin_path ty)
  | AbstractIntroducer (abstract, tyu) ->
    AbstractIntroducer (abstract, qualify_tyu origin_path tyu)
  | Abstract _ | Weak _ -> ty_use

and qualify_ty (origin_path : string list) (ty : ty) : ty =
  match ty with
  | Named (name, ty_uses) ->
    Named (qualify_name origin_path name, List.map (qualify_tyu origin_path) ty_uses)
  | Raw (mode, shape, raw_ty) -> Raw (mode, shape, qualify_raw_ty origin_path raw_ty)

and qualify_raw_ty (origin_path : string list) (raw_ty : raw_ty) : raw_ty =
  match raw_ty with
  | Int -> Int
  | Bool -> Bool
  | Product ty_uses -> Product (List.map (qualify_tyu origin_path) ty_uses)
  | Array ty_use -> Array (qualify_tyu origin_path ty_use)
  | Variant variants ->
    Variant
      (List.map
         (fun { constr_name; constr_args } ->
            { constr_name; constr_args = List.map (qualify_tyu origin_path) constr_args })
         variants)
;;

let rec negate_tyu (ty_use : ty_use) : ty_use =
  match ty_use with
  | Polarised (Plus, mty) -> Polarised (Minus, mty)
  | Polarised (Minus, mty) -> Polarised (Plus, mty)
  | Abstract { negated; name } -> Abstract { negated = not negated; name }
  | AbstractIntroducer (name, ty_use) -> AbstractIntroducer (name, negate_tyu ty_use)
  | Weak { link = { negated; meta } } ->
    let link = { negated = not negated; meta } in
    Weak { link }
;;

(*
 * An inferred weak type variable.
 * Since our inference system will default to data[cbv], we only
 * need to keep track of whether the type is a constructor or destructor.
 * If it is ever compared against a more specific type, it adopts that
 * type's mode and shape information.
 *)
module WeakTyu = struct
  let new_meta_var () : meta_var =
    let id = genint () in
    { id; cell = Inferred { constructor = None; raw_lower_bound = None } }
  ;;

  let new_unknown_tyu () : ty_use =
    let meta = new_meta_var () in
    Weak { link = { negated = false; meta } }
  ;;

  let new_constructor_tyu raw : ty_use =
    let meta = new_meta_var () in
    meta.cell <- Inferred { constructor = Some true; raw_lower_bound = Some raw };
    Weak { link = { negated = false; meta } }
  ;;

  let new_destructor_tyu raw : ty_use =
    let constructor_tyu = new_constructor_tyu raw in
    negate_tyu constructor_tyu
  ;;

  (* checks if there isn't enough information in a tyu to determine
   * some inferred type *)
  let is_unknown tyu =
    match tyu with
    | Weak { link = { meta; _ } } -> begin
      match meta.cell with
      | Inferred { constructor = None; raw_lower_bound = _ }
      | Inferred { constructor = _; raw_lower_bound = None } -> true
      | _ -> false
    end
    | _ -> false
  ;;
end

module Substitute = struct
  let rec tyu_replace (bindings : (string * ty_use) list) (target : ty_use) : ty_use =
    match target with
    | Polarised (polarity, ty) -> Polarised (polarity, ty_replace bindings ty)
    | AbstractIntroducer ({ name; left_focusing }, ty_use) ->
      let new_bindings = List.remove_assoc name bindings in
      AbstractIntroducer ({ name; left_focusing }, tyu_replace new_bindings ty_use)
    | Abstract { negated; name } -> begin
      match List.assoc_opt name bindings with
      | Some ty_use -> if negated then negate_tyu ty_use else ty_use
      | None -> target
    end
    | Weak { link = { negated; meta } } ->
      Weak { link = { negated; meta = meta_var_replace bindings meta } }

  and meta_var_replace (bindings : (string * ty_use) list) (meta : meta_var) : meta_var =
    match meta.cell with
    | Unified tyu ->
      let new_tyu = tyu_replace bindings tyu in
      meta.cell <- Unified new_tyu;
      meta
    | Inferred cons ->
      let constructor =
        match cons.constructor with
        | Some c -> Some c
        | None -> None
      in
      let raw_lower_bound =
        match cons.raw_lower_bound with
        | Some r -> Some (raw_ty_replace bindings r)
        | None -> None
      in
      meta.cell <- Inferred { constructor; raw_lower_bound };
      meta

  and ty_replace (bindings : (string * ty_use) list) (target : ty) : ty =
    match target with
    | Named (name, ty_uses) -> Named (name, List.map (tyu_replace bindings) ty_uses)
    | Raw (mode, shape, raw_ty) -> Raw (mode, shape, raw_ty_replace bindings raw_ty)

  and raw_ty_replace (bindings : (string * ty_use) list) (target : raw_ty) : raw_ty =
    match target with
    | Int -> Int
    | Bool -> Bool
    | Product ty_uses -> Product (List.map (tyu_replace bindings) ty_uses)
    | Array ty_use -> Array (tyu_replace bindings ty_use)
    | Variant variants ->
      Variant
        (List.map
           (fun { constr_name; constr_args } ->
              { constr_name; constr_args = List.map (tyu_replace bindings) constr_args })
           variants)
  ;;

  let resolve_parameterized_ty (ty : ty) (tydef_env : tydef_env) : ty =
    match ty with
    | Raw _ -> ty
    | Named (name, ty_uses) ->
    match Env.lookup_env name tydef_env with
    | None -> raise (TypeNotFound name)
    | Some { origin_path; obj = abstracts, found_ty } ->
      let found_ty = qualify_ty origin_path found_ty in
      if List.length abstracts <> List.length ty_uses
      then
        raise
          (TypeInstantiationFailure (name, List.length abstracts, List.length ty_uses))
      else (
        let bindings = List.combine abstracts ty_uses in
        ty_replace bindings found_ty)
  ;;
end

let canonical_ty (name : name) (ty_uses : ty_use list) (tydef_env : tydef_env) : ty =
  let rec aux name ty_uses =
    match Substitute.resolve_parameterized_ty (Named (name, ty_uses)) tydef_env with
    | Raw _ -> Named (name, ty_uses)
    | Named (new_name, new_tyu_uses) -> aux new_name new_tyu_uses
  in
  aux name ty_uses
;;

let is_variant_ty (ty : ty) (tydef_env : tydef_env) : bool =
  match ty with
  | Raw (_, _, Variant _) -> true
  | Raw _ -> false
  | Named (name, ty_uses) ->
    let canonical = canonical_ty name ty_uses tydef_env in
    (match Substitute.resolve_parameterized_ty canonical tydef_env with
     | Raw (_, _, Variant _) -> true
     | _ -> false)
;;

(* resolved - means there is no chance that the 
 * type can be further resolved
 *)
let rec tyu_is_resolved (tyu : ty_use) : bool =
  match tyu with
  | Polarised (_, ty) -> ty_is_resolved ty
  | AbstractIntroducer (_, tyu) -> tyu_is_resolved tyu
  | Abstract _ -> true
  | Weak { link = { meta; _ } } -> meta_var_is_resolved meta

and meta_var_is_resolved m : bool =
  match m.cell with
  (* inferred meta variables can be further resolved *)
  | Inferred _ -> false
  | Unified tyu -> tyu_is_resolved tyu

and ty_is_resolved (ty : ty) : bool =
  match ty with
  | Named (_, ty_uses) -> List.for_all tyu_is_resolved ty_uses
  | Raw (_, _, raw_ty) -> raw_ty_is_resolved raw_ty

and raw_ty_is_resolved (raw_ty : raw_ty) : bool =
  match raw_ty with
  | Int -> true
  | Bool -> true
  | Product ty_uses -> List.for_all tyu_is_resolved ty_uses
  | Array ty_use -> tyu_is_resolved ty_use
  | Variant variants ->
    List.for_all
      (fun { constr_args; _ } -> List.for_all tyu_is_resolved constr_args)
      variants
;;

let ty_to_raw_ty (ty : ty) (tydef_env : tydef_env) : mode * shape * raw_ty =
  let rec aux ty =
    match ty with
    | Raw (mode, shape, raw_ty) -> mode, shape, raw_ty
    | _ ->
      let resolved_ty = Substitute.resolve_parameterized_ty ty tydef_env in
      aux resolved_ty
  in
  aux ty
;;

(* invariant: this is only ever called on resolved tyus *)
let rec tyu_to_raw_ty_strict (tyu : ty_use) (tydef_env : tydef_env)
  : mode * polarity * shape * raw_ty
  =
  match tyu with
  | Polarised (polarity, ty) ->
    let mode, shape, raw_ty = ty_to_raw_ty ty tydef_env in
    mode, polarity, shape, raw_ty
  | Abstract { name; _ } ->
    let message =
      Printf.sprintf
        "Cannot obtain modal, polarity information of an abstract type variable (name: \
         %s)"
        name
    in
    raise (Error.TypeError { loc = None; message })
  | AbstractIntroducer (_, tyu) ->
    tyu_to_raw_ty_strict
      tyu
      tydef_env (* TODO - emit the information on the abstract variable *)
  | Weak { link = { negated; meta } } ->
  match meta.cell with
  | Unified tyu ->
    let m, p, s, r = tyu_to_raw_ty_strict tyu tydef_env in
    begin match p, negated with
    | Plus, true | Minus, false -> m, Minus, s, r
    | Minus, true | Plus, false -> m, Plus, s, r
    end
  | Inferred _ ->
    let message =
      Printf.sprintf
        "Cannot obtain modal, polarity information of weak type variable %s that has not \
         been fully unified"
        (Pretty.show_ty_use tyu)
    in
    raise (Error.TypeError { loc = None; message })
;;

(* returns whether the tyu is a constructor or destructor of
 * some raw type *)
let rec tyu_to_raw_ty (tyu : ty_use) (tydef_env : tydef_env) : bool * raw_ty =
  match tyu with
  | Polarised (polarity, ty) ->
    let _, shape, raw_ty = ty_to_raw_ty ty tydef_env in
    let is_constructor =
      match polarity, shape with
      | Plus, Data | Minus, Codata -> true
      | Plus, Codata | Minus, Data -> false
    in
    is_constructor, raw_ty
  | Abstract { name; _ } ->
    let message = Printf.sprintf "Cannot convert abstract type %s to raw type" name in
    raise (Error.TypeError { loc = None; message })
  | AbstractIntroducer (_, tyu) -> tyu_to_raw_ty tyu tydef_env
  | Weak { link = { negated; meta } } ->
  match meta.cell with
  | Unified tyu ->
    let is_cons, raw_ty = tyu_to_raw_ty tyu tydef_env in
    is_cons <> negated, raw_ty
  | Inferred { constructor; raw_lower_bound } ->
  match constructor, raw_lower_bound with
  | Some is_constructor, Some raw_ty -> is_constructor <> negated, raw_ty
  | _ ->
    let message =
      Printf.sprintf
        "Cannot convert weak type variable %s to raw type because it does not have \
         enough constraints"
        (Pretty.show_ty_use tyu)
    in
    raise (Error.TypeError { loc = None; message })
;;

let rec is_constructor_tyu ~update (tyu : ty_use) (tydef_env : tydef_env) : bool option =
  match tyu with
  (* TODO: semantics of abstract need to be redone due to abstract introducer *)
  | Abstract { name; _ } ->
    let message =
      Printf.sprintf
        "Cannot determine whether an abstract type variable %s is a constructor or \
         destructor"
        name
    in
    raise (Error.TypeError { loc = None; message })
  | AbstractIntroducer (_, tyu) -> is_constructor_tyu ~update tyu tydef_env
  | Polarised (pol, ty) ->
    let _, shape, _ = ty_to_raw_ty ty tydef_env in
    (match pol, shape with
     | Plus, Data | Minus, Codata -> Some true
     | Plus, Codata | Minus, Data -> Some false)
  | Weak { link = { negated; meta } } ->
  match meta.cell with
  | Unified tyu -> Option.map (( <> ) negated) (is_constructor_tyu ~update tyu tydef_env)
  | Inferred constraints ->
  (* be loose - if the constraint doesn't have a constructor flag, assume it's a constructor *)
  match constraints.constructor with
  | Some is_constructor -> Some (is_constructor <> negated)
  | None ->
    if update
    then begin
      let constructor_val = not negated in
      meta.cell <- Inferred { constraints with constructor = Some constructor_val };
      Some true
    end
    else None
;;

let is_constructor_tyu_forced tyu tydef_env =
  match is_constructor_tyu ~update:true tyu tydef_env with
  | Some is_constructor -> is_constructor
  | None -> assert false (* update makes this case impossible *)
;;

(* should only be None if the tyu is an unknown variable, but we only call this on tyus we know are constructors or destructors *)

(* we will have the standard is_constructor_tyu as a non-updating version *)
let is_constructor_tyu = is_constructor_tyu ~update:false

let rec tyu_equal (tyu1 : ty_use) (tyu2 : ty_use) tydef_env : bool =
  match tyu1, tyu2 with
  | Abstract { negated = neg1; name = name1 }, Abstract { negated = neg2; name = name2 }
    -> neg1 = neg2 && name1 = name2
  | Abstract _, _ | _, Abstract _ -> false
  | AbstractIntroducer _, AbstractIntroducer _ ->
    (* check if the abstractIntroducers are alpha-equivalent, and if not if one is a subtype of the other *)
    failwith "TODO: tyu_equal does not yet support abstract introducers"
  | AbstractIntroducer _, _ | _, AbstractIntroducer _ ->
    failwith "TODO: tyu_equal does not yet support abstract introducers"
  | ( Weak { link = { negated = neg1; meta = meta1 } as link1 }
    , Weak ({ link = { negated = neg2; meta = meta2 } } as weak2) ) ->
    (* check if they are the same meta var, if so check if the negation flags match 
     * 3 cases to consider, since fully resolved tyus are handled above:
     * 1. they are the same meta var - then they are equal iff their negation flags match
     * 2. they are different meta vars, but at least one is fully unsolved
     * 3. both are partially solved - in this case we can attempt to unify the constraints and
     *    complain if not possible
     *)
    if meta1.id = meta2.id
    then neg1 = neg2
    else (
      match meta1.cell, meta2.cell with
      | Unified tyu1, Unified tyu2 ->
        let compared_tyu1 = if neg1 then negate_tyu tyu1 else tyu1 in
        let compared_tyu2 = if neg2 then negate_tyu tyu2 else tyu2 in
        tyu_equal compared_tyu1 compared_tyu2 tydef_env
      | Unified sol1, Inferred _ ->
        let compared_sol1 = if neg1 then negate_tyu sol1 else sol1 in
        unify_weak_with_tyu neg2 meta2 compared_sol1 tydef_env
      | Inferred _, Unified sol2 ->
        let compared_sol2 = if neg2 then negate_tyu sol2 else sol2 in
        unify_weak_with_tyu neg1 meta1 compared_sol2 tydef_env
      | Inferred cons1, Inferred cons2 ->
        (* in this case, there is a chance both cells are updated *)
        let negate = neg1 <> neg2 in
        let unify_result = unify_constraints ~negate cons1 cons2 tydef_env in
        begin match unify_result with
        | Ok (new_cons1, _) ->
          (* unify the first tyu with the second*)
          meta1.cell <- Inferred new_cons1;
          weak2.link <- link1;
          true
        | Error _ -> false
        end)
  | Weak { link = { negated; meta } }, other_tyu
  | other_tyu, Weak { link = { negated; meta } } ->
    (* if the weak tyu is fully unsolved, we can just unify it with the other tyu *)
    unify_weak_with_tyu negated meta other_tyu tydef_env
  | Polarised (polarity1, ty1), Polarised (polarity2, ty2) ->
    polarity1 = polarity2 && ty_equal ty1 ty2 tydef_env

and ty_equal (ty1 : ty) (ty2 : ty) tydef_env : bool =
  match ty1, ty2 with
  | Named (name1, ty_uses1), Named (name2, ty_uses2) ->
    let canonical1 = canonical_ty name1 ty_uses1 tydef_env in
    let canonical2 = canonical_ty name2 ty_uses2 tydef_env in
    (* variants are treated differently - they use curry-style typing *)
    if is_variant_ty canonical1 tydef_env && is_variant_ty canonical2 tydef_env
    then variant_equal canonical1 canonical2 tydef_env
    else (
      let resolved1 = Substitute.resolve_parameterized_ty canonical1 tydef_env in
      let resolved2 = Substitute.resolve_parameterized_ty canonical2 tydef_env in
      ty_equal resolved1 resolved2 tydef_env)
  | Raw (mode1, shape1, raw_ty1), Raw (mode2, shape2, raw_ty2) ->
    mode1 = mode2 && shape1 = shape2 && raw_ty_equal raw_ty1 raw_ty2 tydef_env
  | Raw (m1, s1, r1), ty | ty, Raw (m1, s1, r1) ->
    if is_variant_ty ty tydef_env
    then false
    else (
      (* everything else uses church style typing *)
      let m2, s2, r2 = ty_to_raw_ty ty tydef_env in
      m1 = m2 && s1 = s2 && raw_ty_equal r1 r2 tydef_env)

and variant_equal (ty1 : ty) (ty2 : ty) tydef_env : bool =
  match ty1, ty2 with
  | Named (name1, ty_uses1), Named (name2, ty_uses2) ->
    name1 = name2
    && List.length ty_uses1 = List.length ty_uses2
    && List.for_all2 (fun tyu1 tyu2 -> tyu_equal tyu1 tyu2 tydef_env) ty_uses1 ty_uses2
  | _ -> assert false (* should have been checked by the caller *)

and raw_ty_equal (rty1 : raw_ty) (rty2 : raw_ty) (tydef_env : tydef_env) : bool =
  match rty1, rty2 with
  | Int, Int -> true
  | Bool, Bool -> true
  | Bool, _ | _, Bool -> false
  | Int, _ | _, Int -> false
  | Product tys1, Product tys2 ->
    List.length tys1 = List.length tys2
    && List.for_all2
         (fun ty_use1 ty_use2 -> tyu_equal ty_use1 ty_use2 tydef_env)
         tys1
         tys2
  | Product _, _ | _, Product _ -> false
  | Array ty_use1, Array ty_use2 -> tyu_equal ty_use1 ty_use2 tydef_env
  | Array _, _ | _, Array _ -> false
  | Variant _, Variant _ ->
    (* variants are never directly compared *)
    assert false

and unify_weak_with_tyu
      (negated : bool)
      (meta : meta_var)
      (tyu : ty_use)
      (tydef_env : tydef_env)
  : bool
  =
  let compared_tyu = if negated then negate_tyu tyu else tyu in
  match meta.cell with
  | Unified sol -> tyu_equal sol compared_tyu tydef_env
  | Inferred constraints ->
    let unifiable =
      match constraints.constructor, constraints.raw_lower_bound with
      | None, None -> true
      | Some is_constructor, None ->
        is_constructor == is_constructor_tyu_forced compared_tyu tydef_env
      | None, Some raw_ty ->
        let _, ty_raw_ty = tyu_to_raw_ty compared_tyu tydef_env in
        raw_ty_equal raw_ty ty_raw_ty tydef_env
      | Some is_constructor, Some raw_ty ->
        let _, ty_raw_ty = tyu_to_raw_ty compared_tyu tydef_env in
        is_constructor == is_constructor_tyu_forced compared_tyu tydef_env
        && raw_ty_equal raw_ty ty_raw_ty tydef_env
    in
    if unifiable then meta.cell <- Unified compared_tyu;
    unifiable

and unify_constraints
      ~(negate : bool)
      (cons1 : meta_core_constraints)
      (cons2 : meta_core_constraints)
      (tydef_env : tydef_env)
  : (meta_core_constraints * meta_core_constraints, unit) result
  =
  let constructor_check c1 c2 = c1 = c2 <> negate in
  let constructor_assign c = c <> negate in
  let cons_results =
    match cons1.constructor, cons2.constructor with
    | Some c1, Some c2 ->
      if constructor_check c1 c2 then Ok (Some c1, Some c2) else Error ()
    | Some c, None -> Ok (Some c, Some (constructor_assign c))
    | None, Some c -> Ok (Some (constructor_assign c), Some c)
    | None, None -> Ok (None, None)
  in
  match cons_results with
  | Error () -> Error ()
  | Ok (new_con1, new_con2) ->
  match cons1.raw_lower_bound, cons2.raw_lower_bound with
  | Some r1, Some r2 ->
    if raw_ty_equal r1 r2 tydef_env
    then
      Ok
        ( { constructor = new_con1; raw_lower_bound = Some r1 }
        , { constructor = new_con2; raw_lower_bound = Some r2 } )
    else Error ()
  | Some r, None ->
    Ok
      ( { constructor = new_con1; raw_lower_bound = Some r }
      , { constructor = new_con2; raw_lower_bound = Some r } )
  | None, Some r ->
    Ok
      ( { constructor = new_con1; raw_lower_bound = Some r }
      , { constructor = new_con2; raw_lower_bound = Some r } )
  | None, None ->
    Ok
      ( { constructor = new_con1; raw_lower_bound = None }
      , { constructor = new_con2; raw_lower_bound = None } )
;;

(* Given a constructor's name and arity, look up the first matching type 
 * Note - this returns the polarity of the constructor term
 *)
let type_of_raw_constructor
      (constr_name : string)
      (namespace_path : string list)
      (constr_arity : int)
      (tydef_env : tydef_env)
  : (name * string list * ty * polarity) option
  =
  let property (_, ty) : bool =
    match ty with
    | Raw (_, _, Variant variants) ->
      List.exists
        (fun (v : variant) ->
           v.constr_name = constr_name && List.length v.constr_args = constr_arity)
        variants
    | _ -> false
  in
  let format_result (name, { Env.origin_path; obj = abstracts, ty }) =
    let ty_name = qualify_name origin_path (Base name) in
    let ty = qualify_ty origin_path ty in
    match ty with
    | Raw (_, Data, _) -> ty_name, abstracts, ty, Plus
    | Raw (_, Codata, _) -> ty_name, abstracts, ty, Minus
    | _ -> assert false (* should have been checked by the property function *)
  in
  Option.map format_result (Env.lookup_env_by_property namespace_path property tydef_env)
;;

(* given a constructor and a type, 
 * get the types of the constructor's arguments 
 ** invariant: type must match *)
let args_of_raw_variant (constr : string) (ty : ty) : ty_use list =
  match ty with
  | Raw (_, _, Variant variants) ->
    (match List.find_opt (fun (v : variant) -> v.constr_name = constr) variants with
     | Some v -> v.constr_args
     | None ->
       let message =
         Printf.sprintf "Constructor %s not found in type %s" constr (Pretty.show_ty ty)
       in
       raise (Error.TypeError { loc = None; message }))
  | _ ->
    let message =
      Printf.sprintf
        "Type %s is not a variant type, cannot get constructor %s's argument types"
        (Pretty.show_ty ty)
        constr
    in
    raise (Error.TypeError { loc = None; message })
;;

let type_of_namespaced_constructor
      (constr_name : name)
      (constr_arity : int)
      (tydef_env : tydef_env)
  =
  match constr_name with
  | Base name -> type_of_raw_constructor name [] constr_arity tydef_env
  | Namespaced (path, name) -> type_of_raw_constructor name path constr_arity tydef_env
;;

let args_of_namespaced_variant (constr : name) (ty : ty) : ty_use list =
  match constr with
  | Base name -> args_of_raw_variant name ty
  | Namespaced (_, name) -> args_of_raw_variant name ty
;;

(* TODO: the granularity of this tyu upgrading system can be improved 
 * returns the most specific of two equal tyu's.
 * invariant: must be equal *)
let most_specific_tyu (tyu1 : ty_use) (tyu2 : ty_use) (tydef_env : tydef_env) : ty_use =
  if not (tyu_equal tyu1 tyu2 tydef_env)
  then (
    let message =
      Printf.sprintf
        "Cannot get most specific tyu of two tyus that are not equal: %s and %s"
        (Pretty.show_ty_use tyu1)
        (Pretty.show_ty_use tyu2)
    in
    raise (Error.TypeError { loc = None; message }))
  else (
    match tyu1, tyu2 with
    | Abstract _, Abstract _ -> tyu1 (* tyu_equal ensures that both are equal *)
    | Abstract _, tyu | tyu, Abstract _ -> tyu
    | (Polarised _ as tyu), _ | _, (Polarised _ as tyu) -> tyu
    | AbstractIntroducer _, _ | _, AbstractIntroducer _ ->
      failwith "TODO: most_specific_tyu does not yet support abstract introducers"
    | Weak _, tyu -> tyu)
;;

let validate_tydef (name, abstracts) ty (tydef_env : tydef_env) =
  let rec validate_tydef_ty abs_vars (ty : ty) : unit =
    match ty with
    | Raw (_, _, raw_ty) -> validate_tydef_raw_ty abs_vars raw_ty
    | Named (Base name', ty_uses) when name' = name ->
      (* valid if it's a self use, or some use already possible in the type environment *)
      List.iter (validate_tydef_tyu abs_vars) ty_uses;
      if not (List.length ty_uses = List.length abstracts)
      then
        raise
          (TypeInstantiationFailure (Base name, List.length abstracts, List.length ty_uses))
      else ()
    | Named (n, ty_uses) ->
      List.iter (validate_tydef_tyu abs_vars) ty_uses;
      (match Env.lookup_env n tydef_env with
       | None -> raise (TypeNotFound n)
       (* invariant - any type in the tydef environment is already 
        * well formed *)
       | Some { obj = found_abstracts, _; _ } ->
         if not (List.length ty_uses = List.length found_abstracts)
         then
           raise
             (TypeInstantiationFailure
                (n, List.length found_abstracts, List.length ty_uses))
         else ())
  and validate_tydef_raw_ty abs_vars (raw_ty : raw_ty) : unit =
    match raw_ty with
    | Int -> ()
    | Bool -> ()
    | Product ty_uses -> List.iter (validate_tydef_tyu abs_vars) ty_uses
    | Array ty_use -> validate_tydef_tyu abs_vars ty_use
    | Variant vs ->
      let constr_names = List.map (fun { constr_name; _ } -> constr_name) vs in
      if
        List.length constr_names
        <> List.length (List.sort_uniq String.compare constr_names)
      then raise (MalformedType (Base name, "constructor names must be unique"))
      else
        List.iter
          (fun { constr_args; _ } -> List.iter (validate_tydef_tyu abs_vars) constr_args)
          vs
  and validate_tydef_tyu abs_vars (tyu : ty_use) : unit =
    match tyu with
    | Polarised (_, ty) -> validate_tydef_ty abs_vars ty
    | Abstract { name = abstract_name; _ } ->
      if not (List.mem abstract_name abs_vars)
      then raise (TypeNotFound (Base abstract_name))
      else ()
    | AbstractIntroducer ({ name = abstract_name; _ }, tyu) ->
      validate_tydef_tyu (abstract_name :: abs_vars) tyu
    | Weak _ ->
      let message =
        Printf.sprintf
          "Weak type variables are not allowed in type definitions (in type %s)"
          name
      in
      raise (Error.TypeError { loc = None; message })
  in
  match ty with
  (* ensure that the type doesn't just name itself *)
  | Named (Base name', _) when name' = name ->
    raise (MalformedType (Base name, "type cannot be fully defined in terms of itself"))
  | _ -> validate_tydef_ty abstracts ty
;;

(* used to determine whether a recursive binder is lazy. 
 * if we can't determine whether it is lazy, assume it is not. *)
let rec is_lazy_tyu tyu tydef_env =
  match tyu with
  | Ast.Weak { link = { meta; negated } } -> begin
    match meta.cell with
    | Unified tyu ->
      let tyu_to_compare = if negated then negate_tyu tyu else tyu in
      is_lazy_tyu tyu_to_compare tydef_env
    (* inferred types are always assumed to be data[cbv], so check if it is a destructor *)
    | Inferred { constructor = Some is_constructor; _ } -> not (is_constructor <> negated)
    | Inferred { constructor = None; _ } -> false
  end
  | Ast.Abstract _ -> false
  | Ast.AbstractIntroducer (_, inner_tyu) -> is_lazy_tyu inner_tyu tydef_env
  | Ast.Polarised (pol, ty) ->
    let mode, _, _ = ty_to_raw_ty ty tydef_env in
    (match pol, mode with
     | Plus, By_name -> true
     | Minus, By_value -> true
     | Plus, By_value -> false
     | Minus, By_name -> false)
;;
