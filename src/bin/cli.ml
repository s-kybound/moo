open Cmdliner

let filename_args =
  let doc = "Input programs to evaluate" in
  Arg.(non_empty & pos_all file [] & info [] ~docv:"PROGRAMS" ~doc)
;;

let runner_body = Term.(const Runner.run $ filename_args)

let runner_cmd =
  let doc = "Run a set of moo programs" in
  let info = Cmd.info "run" ~doc in
  Cmd.v info runner_body
;;

let repl_cmd =
  let doc = "REPL for the moo language" in
  let info = Cmd.info "repl" ~doc in
  Cmd.v info Term.(const Repl.start_repl $ const ())
;;

let cmd =
  let doc = "Interpreter for the moo language" in
  let man = [ `S Manpage.s_bugs; `P "Report bugs to <github.com/s-kybound/moo>" ] in
  let info = Cmd.info "moo" ~version:Version.version ~doc ~man ~exits:Cmd.Exit.defaults in
  Cmd.group ~default:runner_body info [ runner_cmd; repl_cmd ]
;;
