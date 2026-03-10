(* Converts a surface syntax tree to the core AST form.
 * Desugars and raises errors on illegal surface syntax,
 * but leaves typechecking to later stages. 
 *)

open Utils.Fresh

let default_ann : Ast.core_ann = Ast.empty_core_ann
let ann_of_surface_loc (loc : Loc.span) : Ast.core_ann = { Ast.loc = Some loc }

let merge_ann (ann1 : Ast.core_ann) (ann2 : Ast.core_ann) : Ast.core_ann =
  let merged_loc =
    match ann1.loc, ann2.loc with
    | Some loc1, Some loc2 -> Some (Loc.merge_loc loc1 loc2)
    | Some loc, None | None, Some loc -> Some loc
    | None, None -> None
  in
  { Ast.loc = merged_loc }
;;

let mk_term ?(loc = default_ann) (node : Ast.core_ann Ast.term_node)
  : Ast.core_ann Ast.term
  =
  loc, node
;;

let mk_command ?(loc = default_ann) (node : Ast.core_ann Ast.command_node)
  : Ast.core_ann Ast.command
  =
  loc, node
;;

let mk_core ~loc (l_term : Ast.core_ann Ast.term) (r_term : Ast.core_ann Ast.term)
  : Ast.core_ann Ast.command
  =
  mk_command ~loc (Ast.Core { l_term; r_term })
;;

let mk_ann ~loc (term : Ast.core_ann Ast.term) (tyu : Ast.ty_use) : Ast.core_ann Ast.term =
  mk_term ~loc (Ast.Ann (term, tyu))
;;

let mk_var ~loc (name : Ast.name) : Ast.core_ann Ast.term =
  mk_term ~loc (Ast.Variable name)
;;

let cutlet_let
      (name : Ast.core_ann Ast.binder)
      (l_term : Ast.core_ann Ast.term)
      (command : Ast.core_ann Ast.command)
  : Ast.core_ann Ast.command
  =
  (* location should be merged *)
  let loc = merge_ann (fst l_term) (fst command) in
  let r_term = mk_term (Ast.Mu (name, command)) in
  mk_core ~loc l_term r_term
;;

let make_proc_type (abstracts : Surface.unify_ty list) (param_types : Ast.ty_use list)
  : Ast.ty_use
  =
  let base_type =
    Ast.Polarised (Ast.Plus, Ast.Raw (Ast.By_value, Ast.Codata, Ast.Product param_types))
  in
  List.fold_right
    (fun abstract_name acc -> Ast.AbstractIntroducer (abstract_name, acc))
    abstracts
    base_type
;;

(* make sure that the recursive binder is not immediately used *)
let rec recursive_definition_is_guarded rec_binder body : bool =
  match body with
  | _, Ast.Variable (Base name) -> not (name = rec_binder)
  | _, Ast.Variable _ -> true
  | _, Ast.Ann (t, _) -> recursive_definition_is_guarded rec_binder t
  | _, Ast.Mu _ -> true
  | _, Ast.Construction _ -> true
  | _, Ast.Tuple _ -> true
  | _, Ast.Matcher _ -> true
  | _, Ast.Num _ -> true
  | _, Ast.Arr _ -> true
  | _, Ast.Exit -> true
  (* invariant - the inner recursive term has already been checked to be guarded *)
  | _, Ast.Rec (Ast.Var (_, name), term) ->
    if name = rec_binder then true else recursive_definition_is_guarded rec_binder term
  | _, Ast.Rec (Ast.Wildcard _, term) -> recursive_definition_is_guarded rec_binder term
;;

let rec surface_ty_use_to_ast_ty_use (tyu : Surface.ty_use) : Ast.ty_use =
  match tyu with
  | Surface.Polarised (pol, ty) -> Ast.Polarised (pol, surface_ty_to_ast_ty ty)
  | Surface.Abstract { negated; name } -> Ast.Abstract { negated; name }
  | Surface.AbstractIntroducer (names, ty_use) ->
    List.fold_left
      (fun acc name -> Ast.AbstractIntroducer (name, acc))
      (surface_ty_use_to_ast_ty_use ty_use)
      (List.rev names)

and surface_ty_to_ast_ty (ty : Surface.ty) : Ast.ty =
  match ty with
  | Surface.Named (name, tyu_list) ->
    Ast.Named (name, List.map surface_ty_use_to_ast_ty_use tyu_list)
  | Surface.Raw (mode, shape, raw_ty) ->
    Ast.Raw (mode, shape, surface_raw_ty_to_ast_raw_ty raw_ty)

and surface_raw_ty_to_ast_raw_ty (raw_ty : Surface.raw_ty) : Ast.raw_ty =
  match raw_ty with
  | Surface.Raw64 -> Ast.Raw64
  | Surface.Product tyu_list ->
    Ast.Product (List.map surface_ty_use_to_ast_ty_use tyu_list)
  | Surface.Array tyu -> Ast.Array (surface_ty_use_to_ast_ty_use tyu)
  | Surface.Variant variants ->
    Ast.Variant
      (List.map
         (fun (v : Surface.variant) : Ast.variant ->
            { constr_name = v.constr_name
            ; constr_args = List.map surface_ty_use_to_ast_ty_use v.constr_args
            })
         variants)
;;

let surface_binder_name_to_ast_binder (bn : Surface.binder_name) : Ast.core_ann Ast.binder
  =
  match bn with
  | Surface.Var s -> Ast.Var (default_ann, s)
  | Surface.Wildcard -> Ast.Wildcard default_ann
;;

(*
  Replaces the surface pattern with AST pattern.
  if the binders are typed, gensym fresh names for each binder,
  then return the list of (gensym_name, original_name, ty_use) for each binder,
  so that the caller can insert the appropriate let-bindings for each binder.
 *)
let surface_pattern_to_ast_pattern (pat : Surface.pattern)
  : Ast.core_ann Ast.pattern * (Ast.name * Ast.core_ann Ast.binder * Ast.ty_use) list
  =
  let binder_fold (acc_binders, acc_ty_uses) (binder : Surface.binder) =
    let name = surface_binder_name_to_ast_binder binder.name in
    if List.mem name acc_binders
    then
      raise
        (Error.SyntaxError { span = None; message = "Duplicate binder name in pattern" })
    else (
      match binder.typ with
      | None -> name :: acc_binders, acc_ty_uses
      | Some ty_use ->
        let binder_name = genvar (Pretty.show_binder name) in
        let binding_triple =
          Ast.Base binder_name, name, surface_ty_use_to_ast_ty_use ty_use
        in
        Ast.Var (default_ann, binder_name) :: acc_binders, binding_triple :: acc_ty_uses)
  in
  match pat with
  | Surface.Binder { name; typ = Some ty_use } ->
    let name = surface_binder_name_to_ast_binder name in
    let binder_name = genvar (Pretty.show_binder name) in
    let binding_triple =
      Ast.Base binder_name, name, surface_ty_use_to_ast_ty_use ty_use
    in
    Ast.Binder (Ast.Var (default_ann, binder_name)), [ binding_triple ]
  | Surface.Binder { name; typ = None } ->
    Ast.Binder (surface_binder_name_to_ast_binder name), []
  | Surface.Tup binders ->
    let binders, binder_ty_uses = List.fold_left binder_fold ([], []) binders in
    let binders, binder_ty_uses = List.rev binders, List.rev binder_ty_uses in
    Ast.Tup binders, binder_ty_uses
  | Surface.Constr { pat_name; pat_args } ->
    let pat_args, binder_ty_uses = List.fold_left binder_fold ([], []) pat_args in
    let pat_args, binder_ty_uses = List.rev pat_args, List.rev binder_ty_uses in
    Ast.Constr { pat_name; pat_args }, binder_ty_uses
  | Surface.Numeral n -> Ast.Numeral n, []
;;

let rec surface_term_to_ast_term (t : Surface.term) : Ast.core_ann Ast.term =
  let node = surface_term_to_ast_term_node t in
  ann_of_surface_loc t.loc, node

and surface_term_to_ast_term_node (t : Surface.term) : Ast.core_ann Ast.term_node =
  let ann = ann_of_surface_loc t.loc in
  match t.it with
  | Surface.Num n -> Ast.Num n
  | Surface.Variable name -> Ast.Variable name
  | Surface.Arr terms -> Ast.Arr (List.map surface_term_to_ast_term terms)
  | Surface.Ann (term, ty_use) ->
    Ast.Ann (surface_term_to_ast_term term, surface_ty_use_to_ast_ty_use ty_use)
  | Surface.Exit -> Ast.Exit
  | Surface.Mu ({ name; typ = Some ty_use }, command) ->
    (*
      { x : tyu -> command } is syntactic sugar for
      ( {x -> command} : neg(tyu) ) or
    *)
    let ty_use = surface_ty_use_to_ast_ty_use ty_use in
    let neg_tyu = Type.negate_tyu ty_use in
    let mu =
      mk_term
        ~loc:ann
        (Ast.Mu
           (surface_binder_name_to_ast_binder name, surface_command_to_ast_command command))
    in
    Ast.Ann (mu, neg_tyu)
  | Surface.Mu ({ name; typ = None }, command) ->
    Ast.Mu (surface_binder_name_to_ast_binder name, surface_command_to_ast_command command)
  | Surface.Construction { cons_name; cons_args } ->
    Ast.Construction
      { cons_name; cons_args = List.map surface_term_to_ast_term cons_args }
  | Surface.Tuple terms -> Ast.Tuple (List.map surface_term_to_ast_term terms)
  | Surface.Matcher branches -> Ast.Matcher (make_matcher_body ann branches)
  | Surface.Rec ({ name; typ }, term) ->
    let new_name = surface_binder_name_to_ast_binder name in
    let new_term = surface_term_to_ast_term term in
    (match new_name with
     | Ast.Wildcard _ ->
       raise
         (Error.SyntaxError
            { span = ann.loc
            ; message =
                "Recursive definition cannot use wildcard binder: recursive variable \
                 must be named"
            })
     | Ast.Var (_, s) ->
       if not (recursive_definition_is_guarded s new_term)
       then
         raise
           (Error.SyntaxError
              { span = ann.loc
              ; message =
                  Printf.sprintf
                    "Recursive definition is not guarded: recursive variable %s used \
                     immediately in body"
                    s
              })
       else (
         match typ with
         | None -> Ast.Rec (new_name, new_term)
         | Some ty_use ->
           (* rec |x : typ| body is syntactic sugar for
            * ( rec |x| body : typ )
            *)
           Ast.Ann
             ( mk_term
                 ~loc:ann
                 (Ast.Rec
                    (surface_binder_name_to_ast_binder name, surface_term_to_ast_term term))
             , surface_ty_use_to_ast_ty_use ty_use )))
  | Proc (abstracts, binders, body) ->
    let typs =
      List.map
        (fun ({ typ; _ } : Surface.binder) ->
           match typ with
           | None ->
             raise
               (Error.SyntaxError
                  { span = None; message = "Binder without type in procedure" })
           | Some ty -> surface_ty_use_to_ast_ty_use ty)
        binders
    in
    let proc_type = make_proc_type abstracts typs in
    let untyped_proc =
      mk_term ~loc:ann (Ast.Matcher (make_matcher_body ann [ Surface.Tup binders, body ]))
    in
    Ast.Ann (untyped_proc, proc_type)
  | UnopTerm (op, in_term) ->
    let out_name = genvar "unop_out" in
    let out_term = mk_var ~loc:ann (Ast.Base out_name) in
    let cmd =
      mk_command
        ~loc:ann
        (Ast.Arith (Ast.Unop { op; in_term = surface_term_to_ast_term in_term; out_term }))
    in
    Ast.Mu (Ast.Var (ann, out_name), cmd)
  | BopTerm (op, l_term, r_term) ->
    let out_name = genvar "bop_out" in
    let out_term = mk_var ~loc:ann (Ast.Base out_name) in
    let cmd =
      mk_command
        ~loc:ann
        (Ast.Arith
           (Ast.Bop
              { op
              ; l_term = surface_term_to_ast_term l_term
              ; r_term = surface_term_to_ast_term r_term
              ; out_term
              }))
    in
    Ast.Mu (Ast.Var (ann, out_name), cmd)

and make_matcher_body ann branches =
  (*
      desugar of
      match {
       | (x : ty) ... (z : ty) -> cmd
      }
      is

      match {
      | x_gensym ... z_gensym ->
        let x <- (x_gensym : ty) in
        ...
        let z <- (z_gensym : ty) in
        cmd
      }    
    *)
  List.map
    (fun (pat, cmd) ->
       let ast_pat, binder_ty_uses =
         try surface_pattern_to_ast_pattern pat with
         | Failure message -> raise (Error.SyntaxError { span = ann.loc; message })
       in
       let ast_cmd =
         List.fold_right
           (fun (gensym_binder, original_binder, ty_use) acc_cmd ->
              cutlet_let
                original_binder
                (mk_ann ~loc:ann (mk_var ~loc:ann gensym_binder) ty_use)
                acc_cmd)
           binder_ty_uses
           (surface_command_to_ast_command cmd)
       in
       ast_pat, ast_cmd)
    branches

and surface_command_to_ast_command (cmd : Surface.command) : Ast.core_ann Ast.command =
  let node = surface_command_to_ast_command_node cmd in
  ann_of_surface_loc cmd.loc, node

and surface_command_to_ast_command_node (cmd : Surface.command)
  : Ast.core_ann Ast.command_node
  =
  match cmd.it with
  | Surface.Matchlet { matched_term; matcher_term } ->
    Ast.Core
      { l_term = surface_term_to_ast_term matched_term
      ; r_term = surface_term_to_ast_term matcher_term
      }
  | Surface.Cutlet ({ name; typ }, term, command) ->
    let l_term =
      mk_term
        ~loc:(ann_of_surface_loc cmd.loc)
        (Ast.Mu
           (surface_binder_name_to_ast_binder name, surface_command_to_ast_command command))
    in
    let r_term =
      match typ with
      | None -> surface_term_to_ast_term term
      | Some ty_use ->
        let ann, t_node = surface_term_to_ast_term term in
        mk_term ~loc:ann (Ast.Ann ((ann, t_node), surface_ty_use_to_ast_ty_use ty_use))
    in
    Ast.Core { l_term; r_term }
  | Surface.Ignore (term, rest) ->
    let l_term =
      mk_term
        ~loc:(ann_of_surface_loc cmd.loc)
        (Ast.Mu
           (Ast.Wildcard (ann_of_surface_loc cmd.loc), surface_command_to_ast_command rest))
    in
    let r_term = surface_term_to_ast_term term in
    Ast.Core { l_term; r_term }
  | Surface.Core { l_term; r_term } ->
    Ast.Core
      { l_term = surface_term_to_ast_term l_term
      ; r_term = surface_term_to_ast_term r_term
      }
  | Surface.Arith (Surface.Unop { op; in_term; out_term }) ->
    Ast.Arith
      (Ast.Unop
         { op
         ; in_term = surface_term_to_ast_term in_term
         ; out_term = surface_term_to_ast_term out_term
         })
  | Surface.Arith (Surface.Bop { op; l_term; r_term; out_term }) ->
    Ast.Arith
      (Ast.Bop
         { op
         ; l_term = surface_term_to_ast_term l_term
         ; r_term = surface_term_to_ast_term r_term
         ; out_term = surface_term_to_ast_term out_term
         })
  | Surface.Fork (c1, c2) ->
    Ast.Fork (surface_command_to_ast_command c1, surface_command_to_ast_command c2)
;;

let surface_top_level_item_to_ast_top_level_item
      (f : 'surface -> 'ast)
      (item : 'surface Surface.top_level_item)
  : 'ast Ast.top_level_item
  =
  match item with
  | Surface.Open mod_open -> Ast.Open mod_open
  | Surface.Def def -> Ast.Def (f def)
;;

let rec surface_mod_tli_to_ast_mod_tli (def : Surface.mod_tli) : Ast.core_ann Ast.mod_tli =
  match def with
  | Surface.TermDef ({ name; typ = None }, term) ->
    Ast.TermDef (surface_binder_name_to_ast_binder name, surface_term_to_ast_term term)
  | Surface.TermDef ({ name; typ = Some ty_use }, term) ->
    let term_node =
      Ast.Ann (surface_term_to_ast_term term, surface_ty_use_to_ast_ty_use ty_use)
    in
    let term = ann_of_surface_loc term.loc, term_node in
    Ast.TermDef (surface_binder_name_to_ast_binder name, term)
  | Surface.TypeDef (name, abstracts, ty) ->
    Ast.TypeDef (name, abstracts, surface_ty_to_ast_ty ty)
  | Surface.Term term -> Ast.Term (surface_term_to_ast_term term)

and surface_module_to_ast_module (m : Surface.module_) : Ast.core_ann Ast.module_ =
  List.map (surface_top_level_item_to_ast_top_level_item surface_mod_tli_to_ast_mod_tli) m
;;

let rec surface_sig_tli_to_ast_sig_tli (sig_def : Surface.sig_tli) : Ast.sig_tli =
  match sig_def with
  | Surface.TypeSigDef (name, abstracts, shape, ty_opt) ->
    Ast.TypeSigDef (name, abstracts, shape, Option.map surface_ty_to_ast_ty ty_opt)
  | Surface.TermSigDef ({ name; typ = _ }, ty_use) ->
    (* typ will always be empty *)
    Ast.TermSigDef
      (surface_binder_name_to_ast_binder name, surface_ty_use_to_ast_ty_use ty_use)

and surface_sig_module_to_ast_sig_module (sig_mod : Surface.sig_module) : Ast.sig_module =
  List.map
    (surface_top_level_item_to_ast_top_level_item surface_sig_tli_to_ast_sig_tli)
    sig_mod
;;
