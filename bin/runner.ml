open Moo
open Ast
open Runner

let get_ast filename = Reader.of_file filename |> Core.convert

let run eval_strat val_strat filename =
  let (module J : JUDGEMENTS) =
    match val_strat with
    | `Lazy -> (module Lazy)
    | `Eager -> (module Eager)
  in
  let (module Strategy : EVALUATION_STRATEGY) =
    match eval_strat with
    | `CBN -> (module Make_CBN (J))
    | `CBV -> (module Make_CBV (J))
  in
  filename
  |> get_ast
  |> Strategy.eval (Env.empty_env ()) (* runner assumes empty env *)
  |> Core.Show.show_cut
  |> print_endline
;;
