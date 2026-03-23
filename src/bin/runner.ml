open Moo.Runner

let run files =
  try
    ignore
      (run
         ~in_ty_env:Typechecker.Bidir.empty_type_context
         ~in_term_env:Core.Ir.empty_environment
         files);
    exit 0
  with
  (* TODO: better exception handling *)
  | exn ->
    let error_msg =
      Printf.sprintf
        "Error while running files '%s': %s"
        (String.concat ", " files)
        (Printexc.to_string exn)
    in
    prerr_endline error_msg;
    exit 1
;;
