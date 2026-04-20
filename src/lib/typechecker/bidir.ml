open Syntax
open Ty_ast
open Type
open Converter

(* a cocontextual typechecker that analyses a given program *)

let type_error ?loc message = raise (Syntax.Error.TypeError { loc; message })

let type_mismatch ?loc expected actual msg =
  let message =
    Printf.sprintf
      "Type error: expected %s but got %s. %s"
      (Syntax.Pretty.show_ty_use expected)
      (Syntax.Pretty.show_ty_use actual)
      msg
  in
  type_error ?loc message
;;

let validate_ty (ty : Ast.ty) (tydef_env : tydef_env) : (Ast.ty, string) result =
  try
    ignore (Substitute.resolve_parameterized_ty ty tydef_env);
    Ok ty
  with
  | TypeNotFound name ->
    Error (Printf.sprintf "Type not found: %s" (Pretty.show_name name))
  | TypeInstantiationFailure (name, expected, actual) ->
    Error
      (Printf.sprintf
         "Type instantiation failure: %s expected %d parameters but got %d"
         (Pretty.show_name name)
         expected
         actual)
  | e ->
    Error
      (Printf.sprintf "Unknown error during type validation: %s" (Printexc.to_string e))
;;

let rec validate_tyu (tyu : Ast.ty_use) (tydef_env : tydef_env)
  : (Ast.ty_use, string) result
  =
  let validate_raw_ty raw =
    validate_ty (Ast.Raw (Ast.By_value, Ast.Data, raw)) tydef_env
  in
  match tyu with
  | Ast.Polarised (_, ty) -> begin
    match validate_ty ty tydef_env with
    | Ok _ -> Ok tyu
    | Error msg -> Error msg
  end
  | Ast.AbstractIntroducer (_, inner_tyu) -> begin
    match validate_tyu inner_tyu tydef_env with
    | Ok _ -> Ok tyu
    | Error msg -> Error msg
  end
  | Ast.Abstract _ -> Ok tyu
  | Ast.Weak { link = { meta; _ } } ->
  match meta.cell with
  | Unified tyu -> begin
    match validate_tyu tyu tydef_env with
    | Ok _ -> Ok tyu
    | Error msg -> Error msg
  end
  | Inferred { raw_lower_bound; _ } ->
  match raw_lower_bound with
  | None -> Ok tyu
  | Some raw ->
  match validate_raw_ty raw with
  | Ok _ -> Ok tyu
  | Error msg -> Error msg
;;

(* check if a recursive name in a recursive term appears in an unguarded position, outside
 * of a destructor. This is because destructors are considered inert.
 * if it does, the entire type must be lazily constructed
 *)
let recursive_name_in_unguarded_position (name : string) (term : typed_term) : bool =
  (* invariant - aux_term is only called on terms that are not in guarded positions *)
  let rec aux_term (term : typed_term) : bool =
    let _, node = term in
    match node with
    | Ast.Variable (Base name') -> name = name'
    | Ast.Variable (Namespaced _) -> false
    | Ast.Construction { cons_args; _ } -> List.exists aux_term cons_args
    | Ast.Tuple terms -> List.exists aux_term terms
    | Ast.Matcher _ -> false
    | Ast.Num _ -> false
    | Ast.Bool _ -> false
    | Ast.Rec (tbinder, tterm) -> begin
      match tbinder with
      | Ast.Var (_, name') -> if name = name' then false else aux_term tterm
      | Ast.Wildcard _ -> aux_term tterm
    end
    | Ast.Arr terms -> List.exists aux_term terms
    | Ast.Ann (term, _) -> aux_term term
    | Ast.Exit -> false
    | Ast.Mu (tbinder, command) ->
    match tbinder with
    | Ast.Var (_, binder_name) ->
      if binder_name = name then false else aux_command command
    | Ast.Wildcard _ -> aux_command command
  and aux_command (command : typed_command) : bool =
    let _, node = command in
    match node with
    | Ast.Core { l_term; r_term } -> aux_term l_term || aux_term r_term
    | Ast.Fork (cmd1, cmd2) -> aux_command cmd1 || aux_command cmd2
    | Ast.Arith arith_cmd ->
    match arith_cmd with
    | Ast.Unop { in_term; out_term; _ } -> aux_term in_term || aux_term out_term
    | Ast.Bop { l_term; r_term; out_term; _ } ->
      aux_term l_term || aux_term r_term || aux_term out_term
  in
  aux_term term
;;

module IMap = Map.Make (Int)

type context = Ast.ty_use IMap.t

let merge_contexts (ctx1 : context) (ctx2 : context) : context =
  IMap.union
    (fun _id _tyu1 _tyu2 ->
       (* two instance of the same usage should not happen, as each use should be linear *)
       assert false)
    ctx1
    ctx2
;;

let add_to_context id tyu ctx = merge_contexts ctx (IMap.singleton id tyu)
let remove_from_context id ctx = IMap.remove id ctx
let empty_context () : context = IMap.empty

exception UnderspecifiedTypeError
exception SynthOtherSide

let annotate (term : typed_term) (tyu : Ast.ty_use) : typed_term = set_term_ty term tyu

(* Workflow - synthesize takes in a set of invariants, and determines the type of an expression.
 *            it returns the demands in order to have that expression have that type 
 *            it also returns the annotated terms themselves *)
let rec synthesize
          (knowledge : context)
          (expr : typed_term)
          (tydef_env : tydef_env)
          (ty_env : ty_env)
          (implicit_polarity : Ast.polarity option)
  : typed_term * Syntax.Ast.ty_use * context
  =
  let annotate_with = annotate expr in
  let ann, node = expr in
  match node with
  (* variables *)
  | Ast.Variable (Namespaced _ as n) -> begin
    match Env.lookup_env n ty_env with
    | None ->
      type_error
        ?loc:ann.loc
        (Printf.sprintf "Namespaced variable %s not found" (Pretty.show_name n))
    | Some { origin_path; obj = tyu } ->
      let tyu = Type.qualify_tyu origin_path tyu in
      annotate_with tyu, tyu, empty_context ()
  end
  | Ast.Variable (Base _) ->
    (match ann.unique_id with
     | None -> assert false (* impossible case *)
     | Some unique_id ->
     match IMap.find_opt unique_id knowledge with
     | Some ty_use -> annotate_with ty_use, ty_use, empty_context ()
     | None -> raise UnderspecifiedTypeError)
  | Ast.Exit ->
    let tyu = WeakTyu.new_destructor_tyu Int implicit_polarity in
    annotate_with tyu, tyu, empty_context ()
  (* upshifts - synthesizing annotated terms *)
  | Ast.Ann (tterm, ty_use) -> begin
    match validate_tyu ty_use tydef_env with
    | Error msg ->
      type_error
        ?loc:ann.loc
        (Printf.sprintf "synthesize: annotation has invalid type: %s" msg)
    | Ok _ ->
      let checked_term, demands =
        check knowledge tterm ty_use tydef_env ty_env implicit_polarity
      in
      (* we can remove the annotations here *)
      checked_term, ty_use, demands
  end
  | Ast.Rec (Ast.Wildcard _, _) -> assert false (* impossible case, rejected by syntax *)
  | Ast.Rec ((Ast.Var (_, name) as tbinder), tterm) ->
    let inner_expr, inferred_tyu, demands =
      synthesize knowledge tterm tydef_env ty_env implicit_polarity
    in
    let relevant_ids = binder_ids_of_binder tbinder in
    let usage_tyus = List.map (fun id -> IMap.find id demands) relevant_ids in
    let out_tyu =
      match meet_tyu (inferred_tyu :: usage_tyus) tydef_env with
      | None ->
        type_error
          ?loc:ann.loc
          (Printf.sprintf
             "synthesize: type mismatch between usages of recursive binder %s: %s"
             name
             (String.concat ", " (List.map Syntax.Pretty.show_ty_use usage_tyus)))
      | Some ty_use -> ty_use
    in
    if
      recursive_name_in_unguarded_position name tterm
      && not (Type.is_lazy_tyu out_tyu tydef_env)
    then
      type_error
        ?loc:ann.loc
        (Printf.sprintf
           "synthesize: recursive binder %s appears in an unguarded position and has \
            non-lazy type %s"
           name
           (Syntax.Pretty.show_ty_use out_tyu))
    else (
      (* remove the binder usages from the demands *)
      let new_demands =
        List.fold_left (fun acc id -> remove_from_context id acc) demands relevant_ids
      in
      let expr = ann, Ast.Rec (tbinder, inner_expr) in
      annotate expr out_tyu, out_tyu, new_demands)
  | Ast.Mu (tbinder, tcommand) ->
    let tcommand, demands = typecheck_command knowledge tcommand tydef_env ty_env in
    let relevant_ids = binder_ids_of_binder tbinder in
    if List.is_empty relevant_ids
    then (
      let expr = ann, Ast.Mu (tbinder, tcommand) in
      let unknown_tyu = WeakTyu.new_unknown_tyu implicit_polarity in
      annotate expr unknown_tyu, unknown_tyu, demands)
    else (
      let usage_tyus = List.map (fun id -> IMap.find id demands) relevant_ids in
      let out_tyu =
        match meet_tyu usage_tyus tydef_env with
        | None ->
          type_error
            ?loc:ann.loc
            (Printf.sprintf
               "synthesize: type mismatch between usages of binder %s: %s"
               (match tbinder with
                | Ast.Var (_, name) -> name
                | Ast.Wildcard _ -> "_")
               (String.concat ", " (List.map Syntax.Pretty.show_ty_use usage_tyus)))
        | Some ty_use -> Type.negate_tyu ty_use
      in
      begin match is_constructor_tyu out_tyu tydef_env with
      | Some true -> raise SynthOtherSide
      | Some false | None ->
        let new_demands =
          List.fold_left (fun acc id -> remove_from_context id acc) demands relevant_ids
        in
        let expr = ann, Ast.Mu (tbinder, tcommand) in
        annotate expr out_tyu, out_tyu, new_demands
      end)
  | Ast.Matcher branches ->
    let negated_polarity =
      Option.map
        (fun p ->
           match p with
           | Ast.Plus -> Ast.Minus
           | Ast.Minus -> Ast.Plus)
        implicit_polarity
    in
    let new_branches, type_uses, demands =
      List.fold_left
        (fun (branches_acc, type_uses_acc, demands_acc) (pattern, command) ->
           let new_command, requested_tyu, new_demands =
             match pattern with
             | Ast.Numeral _ ->
               let cmd, out_demands =
                 typecheck_command knowledge command tydef_env ty_env
               in
               cmd, WeakTyu.new_constructor_tyu Int negated_polarity, out_demands
             | Ast.Boolean _ ->
               let cmd, out_demands =
                 typecheck_command knowledge command tydef_env ty_env
               in
               cmd, WeakTyu.new_constructor_tyu Bool negated_polarity, out_demands
             | Ast.Binder binder ->
               let cmd, new_demands =
                 typecheck_command knowledge command tydef_env ty_env
               in
               let unique_ids = binder_ids_of_binder binder in
               if List.is_empty unique_ids
               then cmd, WeakTyu.new_unknown_tyu negated_polarity, new_demands
               else (
                 let usage_tyus =
                   List.map (fun id -> IMap.find id new_demands) unique_ids
                 in
                 let out_tyu =
                   match meet_tyu usage_tyus tydef_env with
                   | None ->
                     let msg =
                       Printf.sprintf
                         "synthesize: type mismatch between usages of binder in pattern: \
                          %s"
                         (String.concat
                            ", "
                            (List.map Syntax.Pretty.show_ty_use usage_tyus))
                     in
                     type_error ?loc:ann.loc msg
                   | Some ty_use -> ty_use
                 in
                 if not (Type.is_constructor_tyu_forced out_tyu tydef_env)
                 then type_error ?loc:ann.loc "variable is not a constructed item"
                 else (
                   let new_demands =
                     List.fold_left
                       (fun acc id -> remove_from_context id acc)
                       new_demands
                       unique_ids
                   in
                   cmd, out_tyu, new_demands))
             | Ast.Tup subpats ->
               let cmd, new_demands =
                 typecheck_command knowledge command tydef_env ty_env
               in
               let out_tyus =
                 List.map
                   (fun subpat ->
                      let unique_ids = binder_ids_of_binder subpat in
                      if List.is_empty unique_ids
                      then WeakTyu.new_unknown_tyu negated_polarity
                      else (
                        let usage_tyus =
                          List.map (fun id -> IMap.find id new_demands) unique_ids
                        in
                        match meet_tyu usage_tyus tydef_env with
                        | None ->
                          let msg =
                            Printf.sprintf
                              "synthesize: type mismatch between usages of binder in \
                               pattern: %s"
                              (String.concat
                                 ", "
                                 (List.map Syntax.Pretty.show_ty_use usage_tyus))
                          in
                          type_error ?loc:ann.loc msg
                        | Some ty_use -> ty_use))
                   subpats
               in
               let new_demands =
                 List.fold_left
                   (fun acc subpat ->
                      let unique_ids = binder_ids_of_binder subpat in
                      List.fold_left
                        (fun acc id -> remove_from_context id acc)
                        acc
                        unique_ids)
                   new_demands
                   subpats
               in
               ( cmd
               , WeakTyu.new_constructor_tyu (Product out_tyus) negated_polarity
               , new_demands )
             | Ast.Constr { pat_name; pat_args } ->
             match
               type_of_namespaced_constructor pat_name (List.length pat_args) tydef_env
             with
             | None ->
               let msg =
                 Printf.sprintf
                   "synthesize: type for variant %s with arity %d not found"
                   (Syntax.Pretty.show_name pat_name)
                   (List.length pat_args)
               in
               type_error ?loc:ann.loc msg
             | Some (ty_name, abs_tys, ty, _) ->
               let new_bindings =
                 List.map (fun abs -> abs, WeakTyu.new_unknown_tyu None) abs_tys
               in
               let variant_tys =
                 args_of_namespaced_variant pat_name ty
                 |> List.map (Substitute.tyu_replace new_bindings)
               in
               if List.length variant_tys <> List.length pat_args
               then (
                 let msg =
                   Printf.sprintf
                     "synthesize: arity mismatch for pattern constructor %s: expected %d \
                      but got %d"
                     (Syntax.Pretty.show_name pat_name)
                     (List.length variant_tys)
                     (List.length pat_args)
                 in
                 type_error ?loc:ann.loc msg)
               else (
                 (* using the types we have just discovered, IF the types are fully resolved, we
                  * inject them into the term *)
                 let new_knowledge =
                   List.fold_left2
                     (fun ctx_acc pat_arg arg_tyu ->
                        if not (tyu_is_resolved arg_tyu)
                        then ctx_acc
                        else (
                          let unique_ids = binder_ids_of_binder pat_arg in
                          List.fold_left
                            (fun ctx_acc id -> add_to_context id arg_tyu ctx_acc)
                            ctx_acc
                            unique_ids))
                     knowledge
                     pat_args
                     variant_tys
                 in
                 let cmd, new_demands =
                   typecheck_command new_knowledge command tydef_env ty_env
                 in
                 let out_tyus =
                   List.map
                     (fun subpat ->
                        let unique_ids = binder_ids_of_binder subpat in
                        if List.is_empty unique_ids
                        then WeakTyu.new_unknown_tyu None
                        else (
                          let usage_tyus =
                            List.map (fun id -> IMap.find id new_demands) unique_ids
                          in
                          match meet_tyu usage_tyus tydef_env with
                          | None ->
                            let msg =
                              Printf.sprintf
                                "synthesize: type mismatch between usages of binder in \
                                 pattern: %s"
                                (String.concat
                                   ", "
                                   (List.map Syntax.Pretty.show_ty_use usage_tyus))
                            in
                            type_error ?loc:ann.loc msg
                          | Some ty_use -> ty_use))
                     pat_args
                 in
                 (* finally, we inject these back into the expected type *)
                 let acquired_tyu =
                   tyu_of_instantiated_namespaced_variant
                     (ty_name, abs_tys)
                     ty
                     (pat_name, out_tyus)
                     tydef_env
                 in
                 let new_demands =
                   List.fold_left
                     (fun acc subpat ->
                        let unique_ids = binder_ids_of_binder subpat in
                        List.fold_left
                          (fun acc id -> remove_from_context id acc)
                          acc
                          unique_ids)
                     new_demands
                     pat_args
                 in
                 cmd, acquired_tyu, new_demands)
           in
           ( (pattern, new_command) :: branches_acc
           , requested_tyu :: type_uses_acc
           , merge_contexts demands_acc new_demands ))
        ([], [], empty_context ())
        branches
    in
    begin match meet_tyu type_uses tydef_env with
    | None ->
      let message =
        Printf.sprintf
          "synthesize: type mismatch between branches of matcher: %s"
          (String.concat ", " (List.map Syntax.Pretty.show_ty_use type_uses))
      in
      type_error ?loc:ann.loc message
    | Some out_tyu ->
      let matcher_tyu = Type.negate_tyu out_tyu in
      let expr = ann, Ast.Matcher (List.rev new_branches) in
      annotate expr matcher_tyu, matcher_tyu, demands
    end
  (* constructors *)
  (* constructors will cause the bidirectional typechecker to backtrack 
   * and attempt the other side of a command, with the exception of
   * algebraic data types, which can infer their type, and hence behave as an upshift
   * without an annotation.
   * oh, but the constructors synthesized here should still be in a checkable position. we should attempt to flip
   * if we are typechecking a command.
   *)
  | Ast.Construction { cons_name; cons_args } ->
    let typ =
      type_of_namespaced_constructor cons_name (List.length cons_args) tydef_env
    in
    begin match typ with
    | None ->
      let msg =
        Printf.sprintf
          "synthesize: type for variant %s with arity %d not found"
          (Syntax.Pretty.show_name cons_name)
          (List.length cons_args)
      in
      type_error ?loc:ann.loc msg
    | Some (ty_name, abs_tys, ty, polarity) ->
      (* replace all the abstract types with holes *)
      let bindings = List.map (fun abs -> abs, WeakTyu.new_unknown_tyu None) abs_tys in
      let variant_tys =
        args_of_namespaced_variant cons_name ty
        |> List.map (Substitute.tyu_replace bindings)
      in
      if List.length variant_tys <> List.length cons_args
      then (
        let msg =
          Printf.sprintf
            "synthesize: arity mismatch for constructor %s: expected %d but got %d"
            (Syntax.Pretty.show_name cons_name)
            (List.length variant_tys)
            (List.length cons_args)
        in
        type_error ?loc:ann.loc msg)
      else (
        (* for each constituent term, we now have the expected types of each. 
         * create a new cons_args by checking each term against its expected type *)
        let new_cons_args, new_demands =
          List.fold_left2
            (fun (acc, discoveries) arg expected_ty ->
               let new_arg, new_discoveries =
                 check knowledge arg expected_ty tydef_env ty_env None
               in
               new_arg :: acc, merge_contexts discoveries new_discoveries)
            ([], empty_context ())
            cons_args
            variant_tys
        in
        let ty_with_holes = Ast.Named (ty_name, List.map snd bindings) in
        let tyu = Ast.Polarised (polarity, ty_with_holes) in
        let expr =
          ann, Ast.Construction { cons_name; cons_args = List.rev new_cons_args }
        in
        annotate expr tyu, tyu, new_demands)
    end
  (* constructors. attempt the other side instead *)
  | Ast.Num _ | Ast.Bool _ | Ast.Tuple _ | Ast.Arr _ -> raise SynthOtherSide

(* workflow - given demands, check an expression with a type and output discoveries 
 * invariant - the expected type is valid
 *)
and check
      (knowledge : context)
      (expr : typed_term)
      (expected_type : Syntax.Ast.ty_use)
      (tydef_env : tydef_env)
      (ty_env : ty_env)
      (implicit_polarity : Ast.polarity option)
  : typed_term * context
  =
  let ann, node = expr in
  let annotate_with_tyu expr = annotate expr expected_type in
  match node with
  | Ast.Variable (Namespaced _ as n) -> begin
    match Env.lookup_env n ty_env with
    | None ->
      type_error
        ?loc:ann.loc
        (Printf.sprintf "Namespaced variable %s not found" (Pretty.show_name n))
    | Some { origin_path; obj = tyu } ->
      let tyu = Type.qualify_tyu origin_path tyu in
      (match join_tyu [ expected_type; tyu ] tydef_env with
       | None ->
         type_mismatch
           ?loc:ann.loc
           expected_type
           tyu
           "check: variable expected type mismatch"
       | Some best_tyu -> annotate expr best_tyu, knowledge)
  end
  | Ast.Variable (Base _) ->
    (match ann.unique_id with
     | None -> assert false (* impossible case *)
     | Some unique_id ->
       annotate_with_tyu expr, add_to_context unique_id expected_type (empty_context ()))
  (* constructors *)
  | Ast.Num _ ->
    let target_tyu = WeakTyu.new_constructor_tyu Int implicit_polarity in
    if not (is_constructor_tyu_forced expected_type tydef_env)
    then
      type_mismatch
        ?loc:ann.loc
        expected_type
        target_tyu
        "check: TNum expected type mismatch"
    else if is_subtype_tyu expected_type target_tyu tydef_env
    then annotate_with_tyu expr, empty_context ()
    else
      type_mismatch
        ?loc:ann.loc
        expected_type
        target_tyu
        "check: TNum expected type mismatch"
  | Ast.Bool _ ->
    let target_tyu = WeakTyu.new_constructor_tyu Bool implicit_polarity in
    if not (is_constructor_tyu_forced expected_type tydef_env)
    then
      type_mismatch
        ?loc:ann.loc
        expected_type
        target_tyu
        "check: TBool expected type mismatch"
    else if is_subtype_tyu expected_type target_tyu tydef_env
    then annotate_with_tyu expr, empty_context ()
    else
      type_mismatch
        ?loc:ann.loc
        expected_type
        target_tyu
        "check: TBool expected type mismatch"
  | Ast.Mu (tbinder, tcommand) ->
    let tbinder_ty = Type.negate_tyu expected_type in
    let new_knowledge =
      List.fold_left
        (fun acc id -> add_to_context id tbinder_ty acc)
        knowledge
        (binder_ids_of_binder tbinder)
    in
    let cmd, demands = typecheck_command new_knowledge tcommand tydef_env ty_env in
    let expr = ann, Ast.Mu (tbinder, cmd) in
    annotate expr expected_type, demands
  | Ast.Tuple terms ->
    let target_tyu =
      WeakTyu.new_constructor_tyu
        (Product (List.init (List.length terms) (fun _ -> WeakTyu.new_unknown_tyu None)))
        implicit_polarity
    in
    if not (Type.is_constructor_tyu_forced expected_type tydef_env)
    then
      type_mismatch
        ?loc:ann.loc
        expected_type
        target_tyu
        "check: TTuple expected type mismatch"
    else (
      let is_constructor, raw_ty = Type.tyu_to_raw_ty expected_type tydef_env in
      begin match is_constructor, raw_ty with
      | false, _ ->
        assert false (* impossible, as we just verified that this is a constructor *)
      | _, Product expected_tys ->
        if List.length terms <> List.length expected_tys
        then
          type_mismatch
            ?loc:ann.loc
            expected_type
            (WeakTyu.new_constructor_tyu (Product expected_tys) implicit_polarity)
            "check: TTuple arity mismatch"
        else (
          let new_terms, demands =
            List.fold_left2
              (fun (terms, demands_acc) term expected_ty ->
                 let t, term_demands =
                   check knowledge term expected_ty tydef_env ty_env None
                 in
                 t :: terms, merge_contexts demands_acc term_demands)
              ([], empty_context ())
              terms
              expected_tys
          in
          let expr = ann, Ast.Tuple (List.rev new_terms) in
          annotate expr expected_type, demands)
      | _ ->
        type_mismatch
          ?loc:ann.loc
          expected_type
          (WeakTyu.new_constructor_tyu
             (Product
                (List.init (List.length terms) (fun _ -> WeakTyu.new_unknown_tyu None)))
             implicit_polarity)
          "check: TTuple expected type mismatch"
      end)
  | Ast.Ann (tterm, ty_use) -> begin
    match validate_tyu ty_use tydef_env with
    | Error msg ->
      type_error
        ?loc:ann.loc
        (Printf.sprintf "check: annotation has invalid type: %s" msg)
    | Ok _ ->
      if not (is_subtype_tyu ty_use expected_type tydef_env)
      then
        type_mismatch
          ?loc:ann.loc
          expected_type
          ty_use
          "check: TAnn annotation type mismatch with expected type"
      else (
        let checked_term, demands =
          check knowledge tterm ty_use tydef_env ty_env implicit_polarity
        in
        let expr = ann, Ast.Ann (checked_term, ty_use) in
        annotate expr expected_type, demands)
  end
  | Ast.Rec (Ast.Wildcard _, _) -> assert false (* impossible case, rejected by syntax *)
  | Ast.Rec ((Ast.Var (_, name) as tbinder), tterm) ->
    let usage_tyus =
      List.map (fun id -> id, expected_type) (binder_ids_of_binder tbinder)
    in
    let new_knowledge =
      List.fold_left (fun acc (id, ty) -> add_to_context id ty acc) knowledge usage_tyus
    in
    let term, demands =
      check new_knowledge tterm expected_type tydef_env ty_env implicit_polarity
    in
    let expr = ann, Ast.Rec (tbinder, term) in
    if
      recursive_name_in_unguarded_position name tterm
      && not (Type.is_lazy_tyu expected_type tydef_env)
    then
      type_error
        ?loc:ann.loc
        (Printf.sprintf
           "check: recursive binder %s appears in an unguarded position and has non-lazy \
            type %s"
           name
           (Syntax.Pretty.show_ty_use expected_type))
    else annotate expr expected_type, demands
  | Ast.Construction { cons_name; cons_args } ->
    let typ =
      type_of_namespaced_constructor cons_name (List.length cons_args) tydef_env
    in
    begin match typ with
    | None ->
      let msg =
        Printf.sprintf
          "check: type for constructor %s with arity %d not found"
          (Syntax.Pretty.show_name cons_name)
          (List.length cons_args)
      in
      type_error ?loc:ann.loc msg
    | Some (name, abs_tys, _, polarity) ->
      let new_abstracts =
        List.map (fun abs -> abs, WeakTyu.new_unknown_tyu None) abs_tys
      in
      let compared_tyu =
        Ast.Polarised (polarity, Ast.Named (name, List.map snd new_abstracts))
      in
      if is_subtype_tyu compared_tyu expected_type tydef_env
      then annotate expr compared_tyu, empty_context ()
      else
        type_mismatch
          ?loc:ann.loc
          expected_type
          compared_tyu
          "check: constructor type mismatch with expected type"
    end
  | Ast.Arr terms ->
    if not (Type.is_constructor_tyu_forced expected_type tydef_env)
    then
      type_mismatch
        ?loc:ann.loc
        expected_type
        (WeakTyu.new_constructor_tyu
           (Array (WeakTyu.new_unknown_tyu None))
           implicit_polarity)
        "check: TArr expected type mismatch"
    else (
      let is_constructor, raw_ty = Type.tyu_to_raw_ty expected_type tydef_env in
      begin match is_constructor, raw_ty with
      | false, _ ->
        assert false (* impossible, as we just verified that this is a constructor *)
      | _, Array expected_elem_ty ->
        let new_terms, demands =
          List.fold_left
            (fun (terms, demands_acc) term ->
               let t, term_demands =
                 check knowledge term expected_elem_ty tydef_env ty_env None
               in
               t :: terms, merge_contexts demands_acc term_demands)
            ([], empty_context ())
            terms
        in
        let expr = ann, Ast.Arr (List.rev new_terms) in
        annotate expr expected_type, demands
      | _ ->
        type_mismatch
          ?loc:ann.loc
          expected_type
          (WeakTyu.new_constructor_tyu
             (Array (WeakTyu.new_unknown_tyu None))
             implicit_polarity)
          "check: TArr expected type mismatch"
      end)
  (* destructors - all downshifts here *)
  | Ast.Exit | Ast.Matcher _ ->
    let synthesized_term, synthesized_tyu, demands =
      synthesize knowledge expr tydef_env ty_env implicit_polarity
    in
    if not (is_subtype_tyu synthesized_tyu expected_type tydef_env)
    then
      type_mismatch
        ?loc:ann.loc
        expected_type
        synthesized_tyu
        "check: destructor expected type mismatch"
    else annotate synthesized_term synthesized_tyu, demands

and typecheck_command
      (knowledge : context)
      (command : typed_command)
      (tydef_env : tydef_env)
      (ty_env : ty_env)
  : typed_command * context
  =
  let ann, node = command in
  let rec typecheck_command_aux synth_term check_term expression_side previous_error =
    try
      let synth_mode, check_mode =
        if expression_side = `Left
        then Some Ast.Plus, Some Ast.Minus
        else Some Ast.Minus, Some Ast.Plus
      in
      let synth_expr, synth_tyu, synth_demands =
        synthesize knowledge synth_term tydef_env ty_env synth_mode
      in
      let check_expr, check_demands =
        check knowledge check_term (Type.negate_tyu synth_tyu) tydef_env ty_env check_mode
      in
      let out_demands = merge_contexts synth_demands check_demands in
      match expression_side with
      | `Left ->
        let cmd = Ast.Core { l_term = synth_expr; r_term = check_expr } in
        mk_command ann cmd, out_demands
      | `Right ->
        let cmd = Ast.Core { l_term = check_expr; r_term = synth_expr } in
        mk_command ann cmd, out_demands
    with
    | SynthOtherSide ->
      if previous_error = `First_attempt
      then (
        let new_direction =
          match expression_side with
          | `Left -> `Right
          | `Right -> `Left
        in
        typecheck_command_aux check_term synth_term new_direction `AttemptOtherSide)
      else begin
        let left_term, right_term =
          if expression_side = `Left
          then synth_term, check_term
          else check_term, synth_term
        in
        match previous_error with
        | `First_attempt -> assert false (* impossible case *)
        | `AttemptOtherSide ->
          let message =
            Printf.sprintf
              "typecheck_command: Command is underspecified, cannot determine the type \
               of the destructor. Left term: %s, Right term: %s"
              (Syntax.Pretty.show_term ~ann_show:(fun _ s -> s) left_term)
              (Syntax.Pretty.show_term ~ann_show:(fun _ s -> s) right_term)
          in
          type_error ?loc:ann.loc message
        | `Underspecified ->
          let message =
            Printf.sprintf
              "typecheck_command: Command is underspecified. Left term: %s, Right term: \
               %s"
              (Syntax.Pretty.show_term ~ann_show:(fun _ s -> s) left_term)
              (Syntax.Pretty.show_term ~ann_show:(fun _ s -> s) right_term)
          in
          type_error ?loc:ann.loc message
      end
    | UnderspecifiedTypeError ->
      if previous_error = `First_attempt
      then (
        let new_direction =
          match expression_side with
          | `Left -> `Right
          | `Right -> `Left
        in
        typecheck_command_aux check_term synth_term new_direction `AttemptOtherSide)
      else (
        match previous_error with
        | `First_attempt -> assert false (* impossible case *)
        | _ ->
          let left_term, right_term =
            if expression_side = `Left
            then synth_term, check_term
            else check_term, synth_term
          in
          let message =
            Printf.sprintf
              "typecheck_command: command is underspecified. Left term: %s, Right term: \
               %s"
              (Syntax.Pretty.show_term ~ann_show:(fun _ s -> s) left_term)
              (Syntax.Pretty.show_term ~ann_show:(fun _ s -> s) right_term)
          in
          type_error ?loc:ann.loc message)
  in
  (* Based on the paper, constructors are checkable and 
   * destructors are synthesizable.
   * Hence, we have a backtracking algorithm to attempt a check of the
   * left term to check whether it is a destructor, before retrying if not, or
   * if unable to determine.
   *)
  let dispatch_typecheck_command_aux
        ((_, ex_term) as expression_term : typed_term)
        ((_, cont_term) as continuation_term : typed_term)
    =
    match ex_term, cont_term with
    (* use the annotation to guide the checking *)
    | _, Ast.Ann (_, tyu) -> begin
      match is_constructor_tyu tyu tydef_env with
      | Some true ->
        typecheck_command_aux expression_term continuation_term `Left `First_attempt
      | _ -> typecheck_command_aux continuation_term expression_term `Right `First_attempt
    end
    | Ast.Ann (_, tyu), _ -> begin
      match is_constructor_tyu tyu tydef_env with
      | Some true ->
        typecheck_command_aux continuation_term expression_term `Right `First_attempt
      | _ -> typecheck_command_aux expression_term continuation_term `Left `First_attempt
    end
    (* variable, mu -> synthesize continuation side first *)
    | Ast.Variable _, _ | Ast.Mu _, _ | Ast.Rec _, _ ->
      typecheck_command_aux continuation_term expression_term `Right `First_attempt
    (* destructors, matchers -> synthesize expression side first *)
    | Ast.Exit, _ | Ast.Matcher _, _ ->
      typecheck_command_aux expression_term continuation_term `Left `First_attempt
    (* the only other cases are constructors, synthesize continuation side first *)
    | _ -> typecheck_command_aux continuation_term expression_term `Right `First_attempt
  in
  match node with
  | Ast.Core { l_term; r_term } -> dispatch_typecheck_command_aux l_term r_term
  (* for Arithmetic commands, it is simpler - the out_term is always the destructor *)
  | Ast.Arith
      (Ast.Bop { op = top; l_term = tl_term; r_term = tr_term; out_term = tout_term }) ->
    let tout_term, out_ty_use, out_demands =
      synthesize knowledge tout_term tydef_env ty_env None
    in
    let in_ty_use = Type.negate_tyu out_ty_use in
    let expected_in_ty = WeakTyu.new_destructor_tyu Int None in
    if not (is_subtype_tyu out_ty_use expected_in_ty tydef_env)
    then
      type_mismatch
        ?loc:ann.loc
        (Type.negate_tyu expected_in_ty)
        out_ty_use
        "typecheck_command: arithmetic binary operation expected int output"
    else (
      let tl_term, left_demands =
        check knowledge tl_term in_ty_use tydef_env ty_env None
      in
      let tr_term, right_demands =
        check knowledge tr_term in_ty_use tydef_env ty_env None
      in
      ( mk_command
          ann
          (Ast.Arith
             (Ast.Bop
                { op = top; l_term = tl_term; r_term = tr_term; out_term = tout_term }))
      , merge_contexts out_demands (merge_contexts left_demands right_demands) ))
  | Ast.Arith (Ast.Unop { op = top; in_term = tin_term; out_term = tout_term }) ->
    let tout_term, out_ty_use, out_demands =
      synthesize knowledge tout_term tydef_env ty_env None
    in
    let in_ty_use = Type.negate_tyu out_ty_use in
    let expected_in_ty = WeakTyu.new_destructor_tyu Int None in
    if not (is_subtype_tyu out_ty_use expected_in_ty tydef_env)
    then
      type_mismatch
        ?loc:ann.loc
        (Type.negate_tyu expected_in_ty)
        out_ty_use
        "typecheck_command: arithmetic unary operation expected int output"
    else (
      let tin_term, in_demands =
        check knowledge tin_term in_ty_use tydef_env ty_env None
      in
      ( mk_command
          ann
          (Ast.Arith (Ast.Unop { op = top; in_term = tin_term; out_term = tout_term }))
      , merge_contexts out_demands in_demands ))
  | Ast.Fork (cmd1, cmd2) ->
    let cmd1, ctx1_demands = typecheck_command knowledge cmd1 tydef_env ty_env in
    let cmd2, ctx2_demands = typecheck_command knowledge cmd2 tydef_env ty_env in
    mk_command ann (Ast.Fork (cmd1, cmd2)), merge_contexts ctx1_demands ctx2_demands
;;

let rec tycheck_mod_tli
          (def : typed_mod_tli)
          (knowledge : context)
          (ty_env : ty_env)
          (tydef_env : tydef_env)
  : typed_mod_tli * ty_env * context * tydef_env
  =
  match def with
  | Ast.TermDef (tbinder, tterm) ->
    let tterm, inferred_ty, _synth_demands =
      synthesize knowledge tterm tydef_env ty_env None
    in
    let new_knowledge =
      List.fold_left
        (fun acc id -> add_to_context id inferred_ty acc)
        knowledge
        (binder_ids_of_binder tbinder)
    in
    let new_ty_env =
      match tbinder with
      | Ast.Wildcard _ -> ty_env
      | Ast.Var (_, name) -> Env.extend_env name inferred_ty ty_env
    in
    Ast.TermDef (tbinder, tterm), new_ty_env, new_knowledge, tydef_env
  | Ast.TypeDef (name, abstracts, ty) ->
    (* for now, we reject duplicate type definitions - it is a lot easier to reason about :) *)
    if Env.exists (Base name) tydef_env
    then type_error (Printf.sprintf "type %s is already defined in this module" name)
    else (
      try
        Type.validate_tydef (name, abstracts) ty tydef_env;
        let new_tydef_env = Env.extend_env name (abstracts, ty) tydef_env in
        Ast.TypeDef (name, abstracts, ty), ty_env, knowledge, new_tydef_env
      with
      | Type.TypeNotFound n ->
        type_error (Printf.sprintf "type %s is not found" (Syntax.Pretty.show_name n))
      | Type.TypeInstantiationFailure (name, expected_arity, actual_arity) ->
        type_error
          (Printf.sprintf
             "type %s expects %d arguments but got %d"
             (Syntax.Pretty.show_name name)
             expected_arity
             actual_arity)
      | Type.MalformedType (name, msg) ->
        type_error
          (Printf.sprintf "type %s is malformed: %s" (Syntax.Pretty.show_name name) msg))
  | Ast.Term term ->
    let new_weak_tyu = WeakTyu.new_unknown_tyu None in
    let tterm, _ = check knowledge term new_weak_tyu tydef_env ty_env None in
    (* if the top level term returns an unknown type, it is most likely of form
     * { _ -> ... } where the hole is never used. In this case,
     * we can assign it the data unit type.
     *)
    if WeakTyu.is_unknown new_weak_tyu
    then (
      let unit_tyu = Ast.Polarised (Plus, Ast.Raw (By_value, Data, Product [])) in
      let tterm, _ = check knowledge tterm unit_tyu tydef_env ty_env None in
      Ast.Term tterm, ty_env, knowledge, tydef_env)
    else Ast.Term tterm, ty_env, knowledge, tydef_env

and tycheck_module
      (knowledge : context)
      (top_level_items : typed_module)
      (tydef_env : tydef_env)
      (ty_env : ty_env)
  : typed_module * ty_env * tydef_env
  =
  let rec process_top_level_items
            (defs : typed_mod_tli Ast.top_level_item list)
            (defs_acc : typed_mod_tli Ast.top_level_item list)
            (ty_env : ty_env)
            (knowledge_acc : context)
            (tydef_env_acc : tydef_env)
    : typed_mod_tli Ast.top_level_item list * context * ty_env * tydef_env
    =
    match defs with
    | [] -> List.rev defs_acc, knowledge_acc, ty_env, tydef_env_acc
    | Ast.Def def :: rest ->
      let newdef, new_ty_env, new_knowledge, new_tydef_env =
        tycheck_mod_tli def knowledge_acc ty_env tydef_env_acc
      in
      process_top_level_items
        rest
        (Ast.Def newdef :: defs_acc)
        new_ty_env
        new_knowledge
        new_tydef_env
    | Ast.Open o :: rest ->
      process_top_level_items
        rest
        (Ast.Open o :: defs_acc)
        ty_env
        knowledge_acc
        tydef_env_acc
  in
  let new_top_level_items, _, new_ty_env, after_defs_tydef_env =
    process_top_level_items top_level_items [] ty_env knowledge tydef_env
  in
  new_top_level_items, new_ty_env, after_defs_tydef_env
;;

(* do a second pass over the typechecked module to ensure that all types, even the inferred types,
 * have enough information to be IR-converted *)
let verify_well_typed (modu : typed_module) : unit =
  let check_underspecified ann =
    if WeakTyu.is_unknown (Option.get ann.ty)
    then (
      let message =
        Printf.sprintf
          "inferred type %s is underspecified"
          (Syntax.Pretty.show_ty_use (Option.get ann.ty))
      in
      type_error ?loc:ann.loc message)
    else ()
  in
  let ann_compare (a1, _) (a2, _) =
    Syntax.Loc_utils.compare_opt_span_size_desc a1.loc a2.loc
  in
  let rec verify_top_level_item (item : typed_mod_tli Ast.top_level_item) : unit =
    match item with
    | Ast.Open _ -> ()
    | Ast.Def def -> verify_mod_tli def
  and verify_mod_tli (def : typed_mod_tli) : unit =
    match def with
    | Ast.TermDef (_, tterm) | Ast.Term tterm ->
      let ann, _ = tterm in
      verify_term tterm;
      check_underspecified ann
    | Ast.TypeDef _ -> ()
  and verify_terms (terms : typed_term list) : unit =
    terms |> List.sort ann_compare |> List.iter verify_term
  and verify_commands (cmds : typed_command list) : unit =
    cmds |> List.sort ann_compare |> List.iter verify_command
  and verify_term (term : typed_term) : unit =
    let ann, node = term in
    begin match node with
    | Ast.Variable _ | Ast.Num _ | Ast.Exit | Ast.Bool _ -> ()
    | Ast.Tuple terms -> verify_terms terms
    | Ast.Ann (tterm, _) -> verify_term tterm
    | Ast.Rec (_, tterm) -> verify_term tterm
    | Ast.Mu (_, cmd) -> verify_command cmd
    | Ast.Matcher branches -> branches |> List.map snd |> verify_commands
    | Ast.Construction { cons_args; _ } -> verify_terms cons_args
    | Ast.Arr terms -> verify_terms terms
    end;
    check_underspecified ann
  and verify_command (cmd : typed_command) : unit =
    let _, node = cmd in
    match node with
    | Ast.Core { l_term; r_term } -> verify_terms [ l_term; r_term ]
    | Ast.Arith (Ast.Bop { l_term; r_term; out_term; _ }) ->
      verify_terms [ l_term; r_term; out_term ]
    | Ast.Arith (Ast.Unop { in_term; out_term; _ }) -> verify_terms [ in_term; out_term ]
    | Ast.Fork (cmd1, cmd2) -> verify_commands [ cmd1; cmd2 ]
  in
  List.iter verify_top_level_item modu
;;

type module_type_context =
  { hole_env : tycheck_hole_environment_frame
  ; ty_env : ty_env
  ; tydef_env : tydef_env
  }

let empty_type_context =
  { hole_env = Top; ty_env = Env.empty_env (); tydef_env = Env.empty_env () }
;;

(* given the updated hole environment, add to context all the 
 * top level bindings of the previous module.
 *)
let make_context hole_env (ty_env : ty_env) : context =
  let seen = Hashtbl.create 10 in
  Env.fold_env
    (fun name ty acc ->
       if Hashtbl.mem seen name
       then acc
       else (
         Hashtbl.add seen name ();
         let usages = Converter.get_usages_of_hole_str hole_env name in
         List.fold_left (fun acc id -> IMap.add id ty acc) acc usages))
    ty_env
    IMap.empty
;;

let tycheck_program (modu : Ast.core_ann Ast.module_) (ctx : module_type_context)
  : typed_module * module_type_context
  =
  let modu, hole_env = tycheck_module_of_ast modu ctx.hole_env in
  let context = make_context hole_env ctx.ty_env in
  let out, ty_env, tydef_env = tycheck_module context modu ctx.tydef_env ctx.ty_env in
  verify_well_typed out;
  out, { hole_env; ty_env; tydef_env }
;;

let modularize_env ?local (name : string list) (ty_ctx : module_type_context)
  : module_type_context
  =
  let open Env in
  { hole_env = Option.value ~default:Top local
  ; ty_env = modularize_env name ty_ctx.ty_env
  ; tydef_env = modularize_env name ty_ctx.tydef_env
  }
;;
