open Moo
open Ast
open Runner

let get_ast filename = Reader.of_file filename |> Core.convert

let run_cbv filename =
  filename
  |> get_ast
  |> Call_by_value.eval (Env.empty_env ()) (* runner assumes empty env *)
  |> Core.Show.show_cut
  |> print_endline
;;

let run_cbn filename =
  filename
  |> get_ast
  |> Call_by_name.eval (Env.empty_env ())
  |> Core.Show.show_cut
  |> print_endline
;;
