(** Library to create fresh variables.
 *  Creates fresh variables.
 *)

let prepend_illegal_suffix name = "!" ^ name

let genint : unit -> int =
  let counter = ref 0 in
  fun () ->
    let id = !counter in
    counter := id + 1;
    id
;;

let genvar v =
  let id = genint () in
  prepend_illegal_suffix (v ^ string_of_int id)
;;

let gensym () = prepend_illegal_suffix (genvar "GENSYM")
