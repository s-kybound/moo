let ensure_moo_extension (filename : string) : bool =
  Filename.check_suffix filename ".moo"
;;

let parse_as_moo_module (filename : string) =
  if not (ensure_moo_extension filename)
  then
    failwith (Printf.sprintf "Error: File '%s' does not have a .moo extension." filename)
  else (
    let module_ = Reader.of_file filename in
    let name = Reader.name_of_file filename in
    name, module_)
;;

(* runs a set of modules, given a known type and value environment. 
 * updates the module environments with the modules that were run, 
 * but ends with the local type and value environments of the
 * input modules - useful for the REPL.
 *)
let run ~in_ty_env ~in_term_env (filenames : string list)
  : Typechecker.Bidir.module_type_context * Core.Ir.environment_frame
  =
  let { Typechecker.Bidir.hole_env
      ; ty_env = local_ty_env, mod_ty_env
      ; tydef_env = local_tydef_env, mod_tydef_env
      }
    =
    in_ty_env
  in
  let local_term_env, mod_term_env = in_term_env in
  let safe_ty_env =
    { Typechecker.Bidir.hole_env = Top
    ; ty_env = Syntax.Env.empty_env_local (), mod_ty_env
    ; tydef_env = Syntax.Env.empty_env_local (), mod_tydef_env
    }
  in
  let safe_term_env = Syntax.Env.empty_env_local (), mod_term_env in
  let modules =
    filenames
    |> List.map parse_as_moo_module
    |> List.map (fun (n, m) ->
      let desugared = Syntax.Surface_to_ast.surface_module_to_ast_module m in
      let resolved = Module_.Resolver.replace_module desugared in
      n, resolved)
  in
  let preexisting = Syntax.Env.modules_of_env in_ty_env.tydef_env in
  let sorted_modules =
    (* TODO: here! need to add the already existing modules *)
    try Module_.Dependency.dfs_toposort ~preexisting modules with
    | Module_.Dependency.CyclicDependency cycle ->
      let cycle_str =
        String.concat " -> " (List.map (fun path -> String.concat "::" path) cycle)
      in
      let error_msg = "Error: Cyclic dependencies detected:\n" ^ cycle_str in
      failwith error_msg
    | Module_.Dependency.UndefinedModuleReference (mod_name, ref_name) ->
      let mod_str = String.concat "::" mod_name in
      let ref_str = String.concat "::" ref_name in
      let error_msg =
        Printf.sprintf
          "Error: Module '%s' references undefined module '%s'"
          mod_str
          ref_str
      in
      failwith error_msg
  in
  (* here, everything is sorted. 
   * now we typecheck the modules *)
  let type_context, typechecked_modules =
    List.fold_left
      (fun (ty_ctx, acc) (mod_name, core_mod) ->
         let ty_mod, out_ty_ctx = Typechecker.Bidir.tycheck_program core_mod ty_ctx in
         let cmd = Core.Tycheck_to_ir.tycheck_command_of_module out_ty_ctx ty_mod in
         let new_ty_ctx = Typechecker.Bidir.modularize_env mod_name out_ty_ctx in
         new_ty_ctx, (mod_name, cmd) :: acc)
      (safe_ty_env, [])
      sorted_modules
    |> fun (ctx, cmds) -> ctx, cmds
  in
  (* now we evaluate the typechecked modules in order *)
  let value_context =
    List.fold_left
      (fun value_ctx (mod_name, cmd) ->
         let out_value_ctx = Core.Runner.eval_program cmd value_ctx in
         Syntax.Env.modularize_env mod_name out_value_ctx)
      safe_term_env
      (List.rev typechecked_modules)
  in
  (* now we can splice together the new module environments with our original local environments *)
  let { Typechecker.Bidir.ty_env = _, new_mod_ty_env
      ; tydef_env = _, new_mod_tydef_env
      ; _
      }
    =
    type_context
  in
  let _, new_mod_term_env = value_context in
  let final_ty_env : Typechecker.Bidir.module_type_context =
    { hole_env
    ; ty_env = local_ty_env, new_mod_ty_env
    ; tydef_env = local_tydef_env, new_mod_tydef_env
    }
  in
  let final_term_env : Core.Ir.environment_frame = local_term_env, new_mod_term_env in
  final_ty_env, final_term_env
;;
