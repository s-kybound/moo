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
  | Constructor (unresolved_tyu_state, raw_ty) -> Destructor (unresolved_tyu_state, raw_ty)
  | Destructor (unresolved_tyu_state, raw_ty) -> Constructor (unresolved_tyu_state, raw_ty)
;;

let rec tyu_replace (bindings : (string * ty_use) list) (target : ty_use) : ty_use =
  match target with
  | Polarised (polarity, ty) -> Polarised (polarity, ty_replace bindings ty)
  | Abstract { negated; name } ->
    (match List.assoc_opt name bindings with
     | Some ty_use -> if negated then negate_tyu ty_use else ty_use
     | None -> target)
  | Constructor (unresolved_tyu_state, raw_ty) ->
    Constructor (unresolved_tyu_state, raw_ty_replace bindings raw_ty)
  | Destructor (unresolved_tyu_state, raw_ty) ->
    Destructor (unresolved_tyu_state, raw_ty_replace bindings raw_ty)

and ty_replace (bindings : (string * ty_use) list) (target : ty) : ty =
  match target with
  | Named (name, ty_uses) -> Named (name, List.map (tyu_replace bindings) ty_uses)
  | Raw (mode, shape, raw_ty) -> Raw (mode, shape, raw_ty_replace bindings raw_ty)

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

let ty_to_raw_ty (ty : ty) (tydef_env : tydef_env) : mode * shape * raw_ty =
  let rec aux ty =
    match ty with
    | Raw (mode, shape, raw_ty) -> mode, shape, raw_ty
    | _ ->
      let resolved_ty = resolve_parameterized_ty ty tydef_env in
      aux resolved_ty
  in
  aux ty
;;

let tyu_to_raw_ty (tyu : ty_use) (tydef_env : tydef_env)
  : mode * polarity * shape * raw_ty
  =
  match tyu with
  | Polarised (polarity, ty) ->
    let mode, shape, raw_ty = ty_to_raw_ty ty tydef_env in
    mode, polarity, shape, raw_ty
  | Abstract _ -> assert false (* should not be called on abstract types *)
  | Constructor _ | Destructor _ -> failwith "TODO: only allow when tyu is fully resolved"
;;

let is_constructor_tyu (tyu : ty_use) (tydef_env : tydef_env) : bool =
  match tyu with
  | Constructor _ -> true
  | Destructor _ -> false
  | Abstract _ -> assert false (* should not be called on abstract types *)
  | Polarised (pol, ty) ->
    let _, shape, _ = ty_to_raw_ty ty tydef_env in
    (match pol, shape with
     | Plus, Data | Minus, Codata -> true
     | Plus, Codata | Minus, Data -> false)
;;

let new_constructor_tyu raw : ty_use =
  Constructor ({ mode = ref None; shape = ref None }, raw)
;;

let new_unmoded_constructor_tyu raw shape : ty_use =
  let state = { mode = ref None; shape = ref shape } in
  state.mode := Some By_value;
  Constructor (state, raw)
;;

(* compare both the modes and shapes. if all is compatible, collapse both states into the most informational state *)
let state_equal (state1 : unresolved_tyu_state) (state2 : unresolved_tyu_state) : bool =
  match !(state1.mode), !(state2.mode) with
  | Some m1, Some m2 when m1 <> m2 -> false
  | _ ->
    (match !(state1.shape), !(state2.shape) with
     | Some s1, Some s2 when s1 <> s2 -> false
     | _ ->
       (* if one state has more information, promote the other *)
       (match !(state1.mode), !(state2.mode) with
        | Some m, None -> state2.mode := Some m
        | None, Some m -> state1.mode := Some m
        | _ -> ());
       (match !(state1.shape), !(state2.shape) with
        | Some s, None -> state2.shape := Some s
        | None, Some s -> state1.shape := Some s
        | _ -> ());
       true)
;;

let state_equal_to_mode_shape (state : unresolved_tyu_state) (mode : mode) (shape : shape)
  : bool
  =
  match !(state.mode) with
  | Some m when m <> mode -> false
  | _ ->
    (match !(state.shape) with
     | Some s when s <> shape -> false
     | _ ->
       (* promote state to have this information *)
       state.mode := Some mode;
       state.shape := Some shape;
       true)
;;

let rec tyu_equal (tyu1 : Syntax.Ast.ty_use) (tyu2 : Syntax.Ast.ty_use) tydef_env : bool =
  match tyu1, tyu2 with
  | Abstract { negated = neg1; name = name1 }, Abstract { negated = neg2; name = name2 }
    -> neg1 = neg2 && name1 = name2
  | Abstract _, _ | _, Abstract _ -> false
  | Constructor (state1, raw_ty1), Constructor (state2, raw_ty2)
  | Destructor (state1, raw_ty1), Destructor (state2, raw_ty2) ->
    (* TODO: attempt promotion as much as possible, if not fail *)
    if not (raw_ty_equal raw_ty1 raw_ty2 tydef_env)
    then false
    else state_equal state1 state2
  | Constructor _, Destructor _ | Destructor _, Constructor _ ->
    false (* should never be equal *)
  | Constructor (state, raw_ty1), resolved_tyu | resolved_tyu, Constructor (state, raw_ty1)
    ->
    let mode, polarity, chirality, raw_ty2 = tyu_to_raw_ty resolved_tyu tydef_env in
    (match polarity, chirality with
     | Plus, Codata | Minus, Data -> false
     | Plus, Data | Minus, Codata ->
       if not (raw_ty_equal raw_ty1 raw_ty2 tydef_env)
       then false
       else state_equal_to_mode_shape state mode chirality)
  | Destructor (state, raw_ty1), resolved_tyu | resolved_tyu, Destructor (state, raw_ty1)
    ->
    let mode, polarity, chirality, raw_ty2 = tyu_to_raw_ty resolved_tyu tydef_env in
    (match polarity, chirality with
     | Plus, Codata | Minus, Data -> false
     | Plus, Data | Minus, Codata ->
       if not (raw_ty_equal raw_ty1 raw_ty2 tydef_env)
       then false
       else state_equal_to_mode_shape state mode chirality)
  | _ ->
    let mode1, polarity1, chirality1, raw_ty1 = tyu_to_raw_ty tyu1 tydef_env in
    let mode2, polarity2, chirality2, raw_ty2 = tyu_to_raw_ty tyu2 tydef_env in
    if mode1 <> mode2 || polarity1 <> polarity2 || chirality1 <> chirality2
    then false
    else raw_ty_equal raw_ty1 raw_ty2 tydef_env

and ty_equal (ty1 : Syntax.Ast.ty) (ty2 : Syntax.Ast.ty) tydef_env : bool =
  let mode1, shape1, raw_ty1 = ty_to_raw_ty ty1 tydef_env in
  let mode2, shape2, raw_ty2 = ty_to_raw_ty ty2 tydef_env in
  if mode1 <> mode2 || shape1 <> shape2
  then false
  else raw_ty_equal raw_ty1 raw_ty2 tydef_env

and raw_ty_equal
      (rty1 : Syntax.Ast.raw_ty)
      (rty2 : Syntax.Ast.raw_ty)
      (tydef_env : tydef_env)
  : bool
  =
  match rty1, rty2 with
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
;;

(* Given a constructor's name and arity, look up the first matching type 
 * Invariant - the constructor's namespacing has been resolved
 * Note - this returns the polarity of the constructor term
 *)
let type_of_raw_constructor
      (constr_name : string)
      (constr_arity : int)
      (tydef_env : tydef_env)
  : (kind_binder * ty * polarity) option
  =
  let rec aux (env : tydef_env) =
    match env with
    | Top -> None
    | TyFrame { parent; var; ty = Raw (_mode, shape, Variant variants) as ty } ->
      let is_matching_variant (v : variant) =
        v.constr_name = constr_name && List.length v.constr_args = constr_arity
      in
      (match List.find_opt is_matching_variant variants with
       | Some _ ->
         (match shape with
          | Data -> Some (var, ty, Plus)
          | Codata -> Some (var, ty, Minus))
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
  | Raw (_, _, Variant variants) ->
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

(* TODO: the granularity of this tyu upgrading system can be improved 
 * returns the most specific of two equal tyu's.
 * invariant: must be equal *)
let most_specific_tyu (tyu1 : ty_use) (tyu2 : ty_use) (tydef_env : tydef_env) : ty_use =
  if not (tyu_equal tyu1 tyu2 tydef_env)
  then failwith "most_specific_tyu: types are not equal, cannot determine most specific"
  else (
    match tyu1, tyu2 with
    | Abstract _, Abstract _ -> tyu1 (* tyu_equal ensures that both are equal *)
    | Abstract _, tyu | tyu, Abstract _ -> tyu
    | (Polarised _ as tyu), _ | _, (Polarised _ as tyu) ->
      tyu
      (* 2 equal polarized types have the same specificity, and are all more specific than everything else *)
    | Constructor _, Constructor _ | Destructor _, Destructor _ ->
      tyu1
      (* tyu_equal ensures that both states are compatible, so we can return either *)
    | Constructor _, Destructor _ | Destructor _, Constructor _ -> assert false)
;;
(* should never be equal *)
