open Ty_ast

let bidir_ann_show (ann : typed_ann) str : string =
  let ty_str =
    match ann.ty with
    | None -> ""
    | Some tyu -> Printf.sprintf "(inferred type: %s)" (Syntax.Pretty.show_ty_use tyu)
  in
  let id_str =
    match ann.unique_id with
    | None -> ""
    | Some id -> Printf.sprintf "(unique id: %d)" id
  in
  let binder_id_str =
    match ann.binder_ids with
    | None -> ""
    | Some ids ->
      let ids_str = String.concat ", " (List.map string_of_int ids) in
      Printf.sprintf "(binder ids: %s)" ids_str
  in
  Printf.sprintf "%s%s%s%s" ty_str id_str binder_id_str str
;;

let show_tychecked_program m = Syntax.Pretty.show_program ~ann_show:bidir_ann_show m
