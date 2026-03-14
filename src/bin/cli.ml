open Cmdliner

let filename_arg =
  let doc = "Input program to evaluate" in
  Arg.(required & pos 0 (some file) None & info [] ~docv:"PROGRAM" ~doc)
;;

let runner_body = Term.(const Runner.run $ filename_arg)

let runner_cmd =
  let doc = "Run a moo program" in
  let info = Cmd.info "run" ~doc in
  Cmd.v info runner_body
;;

let repl_cmd =
  let doc = "REPL for the moo language" in
  let info = Cmd.info "repl" ~doc in
  Cmd.v info Term.(const (Repl.start_repl ()))
;;

let cmd =
  let doc = "Interpreter for the moo language" in
  let man = [ `S Manpage.s_bugs; `P "Report bugs to <github.com/s-kybound/moo>" ] in
  let info = Cmd.info "moo" ~version:Version.version ~doc ~man ~exits:Cmd.Exit.defaults in
  Cmd.group ~default:runner_body info [ repl_cmd ]
;;
