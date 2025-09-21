open Moo
open Ast
open Runner

let get_ast filename = Reader.of_file filename |> Core.convert

let run_cbv filename =
  filename |> get_ast |> Call_by_value.eval |> Core.Show.show |> print_endline
;;

let run_cbn filename =
  filename |> get_ast |> Call_by_name.eval |> Core.Show.show |> print_endline
;;
