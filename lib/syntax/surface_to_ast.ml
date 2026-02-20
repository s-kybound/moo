let default_ann : Ast.core_ann = Ast.empty_core_ann
let ann_of_surface_loc (loc : Loc.span) : Ast.core_ann = { Ast.loc = Some loc }

let mk_term (node : Ast.core_ann Ast.term_node) : Ast.core_ann Ast.term =
  default_ann, node
;;

let mk_command (node : Ast.core_ann Ast.command_node) : Ast.core_ann Ast.command =
  default_ann, node
;;

let mk_core (l_term : Ast.core_ann Ast.term) (r_term : Ast.core_ann Ast.term)
  : Ast.core_ann Ast.command
  =
  mk_command (Ast.Core { l_term; r_term })
;;

let mk_ann (term : Ast.core_ann Ast.term) (tyu : Ast.ty_use) : Ast.core_ann Ast.term =
  mk_term (Ast.Ann (term, tyu))
;;

let mk_var (name : Ast.name) : Ast.core_ann Ast.term = mk_term (Ast.Variable name)

let cutlet_let
      (name : Ast.core_ann Ast.binder)
      (l_term : Ast.core_ann Ast.term)
      (command : Ast.core_ann Ast.command)
  : Ast.core_ann Ast.command
  =
  let r_term = mk_term (Ast.Mu (name, command)) in
  mk_core l_term r_term
;;

let rec surface_ty_use_to_ast_ty_use (tyu : Surface.ty_use) : Ast.ty_use =
  match tyu with
  | Surface.Polarised (pol, ty) -> Ast.Polarised (pol, surface_ty_to_ast_ty ty)
  | Surface.Abstract { negated; name } -> Ast.Abstract { negated; name }

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

let gensym =
  let counter = ref 0 in
  fun prefix ->
    let name = Printf.sprintf "\"GENSYM%s_%d" prefix !counter in
    incr counter;
    name
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
    match binder.typ with
    | None -> acc_binders @ [ name ], acc_ty_uses
    | Some ty_use ->
      let binder_name = gensym (Pretty.show_binder name) in
      let binding_triple =
        Ast.Base binder_name, name, surface_ty_use_to_ast_ty_use ty_use
      in
      ( acc_binders @ [ Ast.Var (default_ann, binder_name) ]
      , acc_ty_uses @ [ binding_triple ] )
  in
  match pat with
  | Surface.Binder { name; typ = Some ty_use } ->
    let name = surface_binder_name_to_ast_binder name in
    let binder_name = gensym (Pretty.show_binder name) in
    let binding_triple =
      Ast.Base binder_name, name, surface_ty_use_to_ast_ty_use ty_use
    in
    Ast.Binder (Ast.Var (default_ann, binder_name)), [ binding_triple ]
  | Surface.Binder { name; typ = None } ->
    Ast.Binder (surface_binder_name_to_ast_binder name), []
  | Surface.Tup binders ->
    let binders, binder_ty_uses = List.fold_left binder_fold ([], []) binders in
    Ast.Tup binders, binder_ty_uses
  | Surface.Constr { pat_name; pat_args } ->
    let pat_args, binder_ty_uses = List.fold_left binder_fold ([], []) pat_args in
    Ast.Constr { pat_name; pat_args }, binder_ty_uses
  | Surface.Numeral n -> Ast.Numeral n, []
;;

let rec surface_term_to_ast_term (t : Surface.term) : Ast.core_ann Ast.term =
  let node = surface_term_to_ast_term_node t in
  ann_of_surface_loc t.loc, node

and surface_term_to_ast_term_node (t : Surface.term) : Ast.core_ann Ast.term_node =
  match t.it with
  | Surface.Mu ({ name; typ = Some ty_use }, command) ->
    (*
      { x : tyu -> command } is syntactic sugar for either
      1. ( {x -> command} : neg(tyu) ) or
      2. {
            x_gensym -> 
            let x <- (x_gensym : tyu) in
            command
         }
      I prefer the second desugaring
    *)
    let gensym_name = gensym "gensym" in
    let gensym_var = mk_var (Base gensym_name) in
    let gensym_binder = Ast.Var (default_ann, gensym_name) in
    let term = mk_ann gensym_var (surface_ty_use_to_ast_ty_use ty_use) in
    Ast.Mu
      ( gensym_binder
      , cutlet_let
          (surface_binder_name_to_ast_binder name)
          term
          (surface_command_to_ast_command command) )
  | Surface.Mu ({ name; typ = None }, command) ->
    Ast.Mu (surface_binder_name_to_ast_binder name, surface_command_to_ast_command command)
  | Surface.Variable name -> Ast.Variable name
  | Surface.Construction { cons_name; cons_args } ->
    Ast.Construction
      { cons_name; cons_args = List.map surface_term_to_ast_term cons_args }
  | Surface.Tuple terms -> Ast.Tuple (List.map surface_term_to_ast_term terms)
  | Surface.Matcher branches ->
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
    let ast_branches =
      List.map
        (fun (pat, cmd) ->
           let ast_pat, binder_ty_uses = surface_pattern_to_ast_pattern pat in
           let ast_cmd =
             List.fold_left
               (fun acc_cmd (gensym_binder, original_binder, ty_use) ->
                  cutlet_let
                    original_binder
                    (mk_ann (mk_var gensym_binder) ty_use)
                    acc_cmd)
               (surface_command_to_ast_command cmd)
               binder_ty_uses
           in
           ast_pat, ast_cmd)
        branches
    in
    Ast.Matcher ast_branches
  | Surface.Num n -> Ast.Num n
  | Surface.Rec ({ name; typ = Some ty_use }, term) ->
    (*
      rec |x : typ| body is syntactic sugar for
      ( rec |x| body : typ )
    *)
    Ast.Ann
      ( mk_term
          (Ast.Rec (surface_binder_name_to_ast_binder name, surface_term_to_ast_term term))
      , surface_ty_use_to_ast_ty_use ty_use )
  | Surface.Rec ({ name; typ = None }, term) ->
    Ast.Rec (surface_binder_name_to_ast_binder name, surface_term_to_ast_term term)
  | Surface.Arr terms -> Ast.Arr (List.map surface_term_to_ast_term terms)
  | Surface.Ann (term, ty_use) ->
    Ast.Ann (surface_term_to_ast_term term, surface_ty_use_to_ast_ty_use ty_use)
  | Surface.Done -> Ast.Done

and surface_command_to_ast_command (cmd : Surface.command) : Ast.core_ann Ast.command =
  let node = surface_command_to_ast_command_node cmd in
  ann_of_surface_loc cmd.loc, node

and surface_command_to_ast_command_node (cmd : Surface.command)
  : Ast.core_ann Ast.command_node
  =
  match cmd.it with
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

let rec surface_definition_to_ast_definition (def : Surface.definition)
  : Ast.core_ann Ast.definition
  =
  match def with
  | Surface.TermDef ({ name; typ = None }, term) ->
    Ast.TermDef (surface_binder_name_to_ast_binder name, surface_term_to_ast_term term)
  | Surface.TermDef ({ name; typ = Some ty_use }, term) ->
    let term_node =
      Ast.Ann (surface_term_to_ast_term term, surface_ty_use_to_ast_ty_use ty_use)
    in
    let term = default_ann, term_node in
    Ast.TermDef (surface_binder_name_to_ast_binder name, term)
  | Surface.TypeDef (kind_binder, ty) -> Ast.TypeDef (kind_binder, surface_ty_to_ast_ty ty)
  | Surface.ModuleDef module_def ->
    Ast.ModuleDef
      { name = module_def.name
      ; program = surface_module_to_ast_module module_def.program
      }

and surface_module_to_ast_module (m : Surface.module_) : Ast.core_ann Ast.module_ =
  let defs, cmd_opt = m in
  let ast_defs =
    List.map
      (surface_top_level_item_to_ast_top_level_item surface_definition_to_ast_definition)
      defs
  in
  let ast_cmd_opt = Option.map surface_command_to_ast_command cmd_opt in
  ast_defs, ast_cmd_opt
;;

let rec surface_sig_definition_to_ast_sig_definition (sig_def : Surface.sig_definition)
  : Ast.sig_definition
  =
  match sig_def with
  | Surface.TypeSigDef (kind_binder, shape, ty_opt) ->
    Ast.TypeSigDef (kind_binder, shape, Option.map surface_ty_to_ast_ty ty_opt)
  | Surface.TermSigDef ({ name; typ = _ }, ty_use) ->
    (* typ will always be empty *)
    Ast.TermSigDef
      (surface_binder_name_to_ast_binder name, surface_ty_use_to_ast_ty_use ty_use)
  | Surface.ModuleSigDef module_sig_def ->
    Ast.ModuleSigDef
      { name = module_sig_def.name
      ; interface = surface_sig_module_to_ast_sig_module module_sig_def.interface
      }

and surface_sig_module_to_ast_sig_module (sig_mod : Surface.sig_module) : Ast.sig_module =
  List.map
    (surface_top_level_item_to_ast_top_level_item
       surface_sig_definition_to_ast_sig_definition)
    sig_mod
;;
