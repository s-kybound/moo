open Syntax.Ast

type tydef_env =
  | Top
  | TyFrame of
      { parent : tydef_env
      ; var : kind_binder
      ; ty : ty
      }

let lookup (name : name) (tydef_env : tydef_env) : ty * string list =
  match name with
  | Base name ->
    let rec aux env =
      match env with
      | Top -> failwith "lookup: type not found in environment"
      | TyFrame { parent; var = ty_name, abstracts; ty } ->
        if ty_name = name then ty, abstracts else aux parent
    in
    aux tydef_env
  | Namespaced _ -> failwith "lookup: namespaced types not supported"
;;

let negate_tyu (ty_use : ty_use) : ty_use =
  match ty_use with
  | Polarised (Plus, mty) -> Polarised (Minus, mty)
  | Polarised (Minus, mty) -> Polarised (Plus, mty)
  | Abstract { negated; name } -> Abstract { negated = not negated; name }
  | Unresolved (Destructor raw_ty) -> Unresolved raw_ty
  | Unresolved raw_ty -> Unresolved (Destructor raw_ty)
  | Unmoded (Plus, ty) -> Unmoded (Minus, ty)
  | Unmoded (Minus, ty) -> Unmoded (Plus, ty)
;;

let rec tyu_replace (bindings : (string * ty_use) list) (target : ty_use) : ty_use =
  match target with
  | Polarised (polarity, (mode_opt, ty)) ->
    Polarised (polarity, (mode_opt, ty_replace bindings ty))
  | Abstract { negated; name } ->
    (match List.assoc_opt name bindings with
     | Some ty_use -> if negated then negate_tyu ty_use else ty_use
     | None -> target)
  | Unresolved raw_ty -> Unresolved (raw_ty_replace bindings raw_ty)
  | Unmoded (polarity, ty) -> Unmoded (polarity, ty_replace bindings ty)

and ty_replace (bindings : (string * ty_use) list) (target : ty) : ty =
  match target with
  | Named (name, ty_uses) -> Named (name, List.map (tyu_replace bindings) ty_uses)
  | Raw (shape, raw_ty) -> Raw (shape, raw_ty_replace bindings raw_ty)

and raw_ty_replace (bindings : (string * ty_use) list) (target : raw_ty) : raw_ty =
  match target with
  | Raw64 -> Raw64
  | Product ty_uses -> Product (List.map (tyu_replace bindings) ty_uses)
  | Array ty_use -> Array (tyu_replace bindings ty_use)
  | Variant variants ->
    Variant
      (List.map
         (fun { constr_name; constr_args } ->
            { constr_name; constr_args = List.map (tyu_replace bindings) constr_args })
         variants)
  | Destructor raw_ty -> Destructor (raw_ty_replace bindings raw_ty)
;;

let resolve_parameterized_ty (ty : ty) (tydef_env : tydef_env) : ty =
  match ty with
  | Named (name, ty_uses) ->
    let found_ty, abstracts = lookup name tydef_env in
    if List.length abstracts <> List.length ty_uses
    then failwith "resolve_parameterized_ty: type parameter length mismatch"
    else (
      let bindings = List.combine abstracts ty_uses in
      ty_replace bindings found_ty)
  | Raw _ -> ty
;;

let ty_to_raw_ty (ty : ty) (tydef_env : tydef_env) : shape * raw_ty =
  let rec aux ty =
    match ty with
    | Raw (shape, raw_ty) -> shape, raw_ty
    | _ ->
      let resolved_ty = resolve_parameterized_ty ty tydef_env in
      aux resolved_ty
  in
  aux ty
;;

(* Infers the default mode of a type *)
let infer_mode shape : mode =
  match shape with
  | Data -> By_value
  | Codata -> By_name
;;

let tyu_to_raw_ty (tyu : ty_use) (tydef_env : tydef_env)
  : mode option * (polarity * shape) option * raw_ty
  =
  match tyu with
  | Polarised (polarity, (mode_opt, ty)) ->
    let shape, raw_ty = ty_to_raw_ty ty tydef_env in
    let mode =
      match mode_opt with
      | Some mode -> mode
      | None -> infer_mode shape
    in
    let raw_ty =
      match polarity, shape with
      | Plus, Data | Minus, Codata -> raw_ty
      | Plus, Codata | Minus, Data -> Destructor raw_ty
    in
    Some mode, Some (polarity, shape), raw_ty
  | Unresolved raw_ty -> None, None, raw_ty
  | Unmoded (polarity, ty) ->
    let shape, raw_ty = ty_to_raw_ty ty tydef_env in
    None, Some (polarity, shape), raw_ty
  | Abstract _ -> failwith "tyu_to_raw_ty: cannot convert abstract type to raw type"
;;

let rec tyu_equal (tyu1 : Syntax.Ast.ty_use) (tyu2 : Syntax.Ast.ty_use) tydef_env : bool =
  match tyu1, tyu2 with
  | Abstract { negated = neg1; name = name1 }, Abstract { negated = neg2; name = name2 }
    -> neg1 = neg2 && name1 = name2
  | Abstract _, _ | _, Abstract _ -> false
  | _ ->
    let mode1, polarity_chirality1, raw_ty1 = tyu_to_raw_ty tyu1 tydef_env in
    let mode2, polarity_chirality2, raw_ty2 = tyu_to_raw_ty tyu2 tydef_env in
    (match mode1, mode2 with
     | Some m1, Some m2 when m1 <> m2 -> false
     | _ ->
       (match polarity_chirality1, polarity_chirality2 with
        | Some (pol1, shape1), Some (pol2, shape2) when pol1 <> pol2 || shape1 <> shape2
          -> false
        | _ -> raw_ty_equal raw_ty1 raw_ty2 tydef_env))

and ty_equal (ty1 : Syntax.Ast.ty) (ty2 : Syntax.Ast.ty) tydef_env : bool =
  let shape1, raw_ty1 = ty_to_raw_ty ty1 tydef_env in
  let shape2, raw_ty2 = ty_to_raw_ty ty2 tydef_env in
  if shape1 <> shape2 then false else raw_ty_equal raw_ty1 raw_ty2 tydef_env

and raw_ty_equal
      (rty1 : Syntax.Ast.raw_ty)
      (rty2 : Syntax.Ast.raw_ty)
      (tydef_env : tydef_env)
  : bool
  =
  let rec strip_destructors rty =
    match rty with
    | Destructor (Destructor inner) -> strip_destructors inner
    | _ -> rty
  in
  match strip_destructors rty1, strip_destructors rty2 with
  | Raw64, Raw64 -> true
  | Raw64, _ | _, Raw64 -> false
  | Product tys1, Product tys2 ->
    List.length tys1 = List.length tys2
    && List.for_all2
         (fun ty_use1 ty_use2 -> tyu_equal ty_use1 ty_use2 tydef_env)
         tys1
         tys2
  | Product _, _ | _, Product _ -> false
  | Array ty_use1, Array ty_use2 -> tyu_equal ty_use1 ty_use2 tydef_env
  | Array _, _ | _, Array _ -> false
  | Variant variants1, Variant variants2 ->
    List.length variants1 = List.length variants2
    && List.for_all2
         (fun { constr_name = name1; constr_args = args1 }
           { constr_name = name2; constr_args = args2 } ->
            name1 = name2
            && List.length args1 = List.length args2
            && List.for_all2
                 (fun ty_use1 ty_use2 -> tyu_equal ty_use1 ty_use2 tydef_env)
                 args1
                 args2)
         variants1
         variants2
  | Variant _, _ | _, Variant _ -> false
  | Destructor raw_ty1, Destructor raw_ty2 -> raw_ty_equal raw_ty1 raw_ty2 tydef_env
;;

(* Given a constructor's name and arity, look up the first matching type 
 * Invariant - the constructor's namespacing has been resolved
 *)
let type_of_raw_constructor
      (constr_name : string)
      (constr_arity : int)
      (tydef_env : tydef_env)
  : (kind_binder * ty) option
  =
  let rec aux (env : tydef_env) =
    match env with
    | Top -> None
    | TyFrame { parent; var; ty = Raw (_, Variant variants) as ty } ->
      let is_matching_variant (v : variant) =
        v.constr_name = constr_name && List.length v.constr_args = constr_arity
      in
      (match List.find_opt is_matching_variant variants with
       | Some _ -> Some (var, ty)
       | None -> aux parent)
    | TyFrame { parent; _ } -> aux parent
  in
  aux tydef_env
;;

(* given a constructor and a type, 
 * get the types of the constructor's arguments 
 ** invariant: type must match*)
let args_of_raw_variant (constr : string) (ty : ty) : Syntax.Ast.ty_use list =
  match ty with
  | Raw (_, Variant variants) ->
    (match List.find_opt (fun (v : variant) -> v.constr_name = constr) variants with
     | Some v -> v.constr_args
     | None -> assert false)
  | _ -> assert false
;;

let type_of_namespaced_constructor
      (constr_name : name)
      (constr_arity : int)
      (tydef_env : tydef_env)
  =
  match constr_name with
  | Base name -> type_of_raw_constructor name constr_arity tydef_env
  | Namespaced _ ->
    failwith
      "TODO: namespacing resolution - namespace semantics have not been figured out"
;;

let args_of_namespaced_variant (constr : name) (ty : ty) : Syntax.Ast.ty_use list =
  match constr with
  | Base name -> args_of_raw_variant name ty
  | Namespaced _ ->
    failwith
      "TODO: namespacing resolution - namespace semantics have not been figured out"
;;

(* TODO: the granularity of this tyu upgrading system can be improved *)
let most_specific_tyu (tyu1 : ty_use) (tyu2 : ty_use) (tydef_env : tydef_env) : ty_use =
  if not (tyu_equal tyu1 tyu2 tydef_env)
  then failwith "most_specific_tyu: types are not equal, cannot determine most specific"
  else (
    match tyu1, tyu2 with
    | Abstract _, Abstract _ -> tyu1 (* tyu_equal ensures that both are equal *)
    | Abstract _, tyu | tyu, Abstract _ -> tyu
    | (Polarised (_, (Some _, _)) as tyu), Polarised _
    | Polarised _, (Polarised (_, (Some _, _)) as tyu) ->
      tyu (* A polarised type with a known mode is more specific than one without *)
    | (Polarised _ as tyu), _ | _, (Polarised _ as tyu) ->
      tyu (* Polarised is more specific than Unmoded or Unresolved *)
    | Unmoded _, Unmoded _ -> tyu1 (* both are equally specific *)
    | Unmoded _, _ | _, Unmoded _ -> tyu1 (* Unmoded is more specific than Unresolved *)
    | Unresolved _, Unresolved _ -> tyu1 (* both are equally specific *))
;;
