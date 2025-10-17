open Moo
open Ast
open Runner
open Typechecker

let get_ast filename = Reader.of_file filename |> Core.convert

let run eval_strat val_strat typechecker filename =
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
  let (module Typechecker : TYPECHECKER) =
    match typechecker with
    | `Untyped -> (module Typechecker.Untyped)
    | `Simply_typed -> (module Typechecker.SimplyTyped)
    | `System_f -> (module Typechecker.SystemF)
    | `Hindley_milner -> (module Typechecker.HindleyMilner)
  in
  filename
  |> get_ast
  |> Typechecker.typecheck
  |> Result.fold
       ~ok:(fun typed_ast ->
         typed_ast
         |> Strategy.eval (Env.empty_env ())
         |> Core.Show.show_cut
         |> print_endline)
       ~error:(fun exn ->
         exn |> Printexc.to_string |> Printf.eprintf "Typechecking error: %s\n%!")
;;
