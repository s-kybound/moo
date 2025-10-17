open Cmdliner

let eval_strategy =
  let doc = "Use call-by-name evaluation strategy" in
  let cbn_flag = Arg.info [ "cbn"; "call-by-name" ] ~doc in
  let doc = "Use call-by-value evaluation strategy (default)" in
  let cbv_flag = Arg.info [ "cbv"; "call-by-value" ] ~doc in
  Arg.(value & vflag `CBV [ `CBN, cbn_flag; `CBV, cbv_flag ])
;;

let value_strategy =
  let doc = "Use lazy semantics" in
  let lazy_flag = Arg.info [ "lazy" ] ~doc in
  let doc = "Use eager semantics (default)" in
  let eager_flag = Arg.info [ "eager" ] ~doc in
  Arg.(value & vflag `Eager [ `Lazy, lazy_flag; `Eager, eager_flag ])
;;

let typechecker_strategy =
  let doc = "Use untyped typechecker (default)" in
  let untyped_flag = Arg.info [ "untyped" ] ~doc in
  let doc = "Use simply-typed typechecker" in
  let simply_typed_flag = Arg.info [ "st"; "simply-typed" ] ~doc in
  let doc = "Use system-f typechecker" in
  let system_f_flag = Arg.info [ "sf"; "system-f" ] ~doc in
  let doc = "Use HM typechecker" in
  let hindley_milner_flag = Arg.info [ "HM"; "hindley-milner" ] ~doc in
  Arg.(
    value
    & vflag
        `Untyped
        [ `Untyped, untyped_flag
        ; `Simply_typed, simply_typed_flag
        ; `System_f, system_f_flag
        ; `Hindley_milner, hindley_milner_flag
        ])
;;

let filename_arg =
  let doc = "Input program to evaluate" in
  Arg.(required & pos 0 (some file) None & info [] ~docv:"PROGRAM" ~doc)
;;

let runner_body =
  Term.(
    const Runner.run
    $ eval_strategy
    $ value_strategy
    $ typechecker_strategy
    $ filename_arg)
;;

let runner_cmd =
  let doc = "Run a moo program" in
  let info = Cmd.info "run" ~doc in
  Cmd.v info runner_body
;;

let repl_cmd =
  let doc = "REPL for the moo language" in
  let info = Cmd.info "repl" ~doc in
  Cmd.v
    info
    Term.(const Repl.start_repl $ eval_strategy $ value_strategy $ typechecker_strategy)
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
  let info = Cmd.info "moo" ~version:Utils.version ~doc ~man ~exits:Cmd.Exit.defaults in
  Cmd.group ~default:runner_body info [ repl_cmd; runner_cmd; moo_cmd ]
;;
