open Cmdliner

let eval_strategy =
  let doc = "Use call-by-name evaluation strategy" in
  let cbn_flag = Arg.info [ "cbn"; "call-by-name" ] ~doc in
  let doc = "Use call-by-value evaluation strategy" in
  let cbv_flag = Arg.info [ "cbv"; "call-by-value" ] ~doc in
  Arg.(value & vflag `CBV [ `CBN, cbn_flag; `CBV, cbv_flag ])
;;

let filename_arg =
  let doc = "Input program to evaluate" in
  Arg.(required & pos 0 (some file) None & info [] ~docv:"PROGRAM" ~doc)
;;

let runner_body =
  let runner_main strategy filename =
    match strategy with
    | `CBN ->
      Printf.printf "Running %s with call-by-name strategy\n" filename;
      Runner.run_cbn filename
    | `CBV ->
      Printf.printf "Running %s with call-by-value strategy\n" filename;
      Runner.run_cbv filename
  in
  Term.(const runner_main $ eval_strategy $ filename_arg)
;;

let runner_cmd =
  let doc = "CBN and CBV evaluators for the moo language" in
  let info = Cmd.info "run" ~doc in
  Cmd.v info runner_body
;;

let repl_cmd =
  let doc = "REPL for the moo language" in
  let info = Cmd.info "repl" ~doc in
  let repl_main strategy = Repl.start_repl strategy in
  Cmd.v info Term.(const repl_main $ eval_strategy)
;;

let moo_cmd =
  let doc = "moos for you" in
  let info = Cmd.info "moo" ~doc in
  let mooer () = print_endline "moo" in
  Cmd.v info Term.(const mooer $ const ())
;;

let cmd =
  let doc = "Interpreter for the moo language" in
  let man = [ `S Manpage.s_bugs; `P "Report bugs to <github.com/s-kybound/moo>" ] in
  let version =
    Option.fold
      (Build_info.V1.version ())
      ~none:"development"
      ~some:Build_info.V1.Version.to_string
  in
  let info = Cmd.info "moo" ~version ~doc ~man ~exits:Cmd.Exit.defaults in
  Cmd.group ~default:runner_body info [ repl_cmd; runner_cmd; moo_cmd ]
;;
