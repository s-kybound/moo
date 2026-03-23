type position =
  { file : string option
  ; line : int
  ; col : int
  }

type span =
  { start_pos : position
  ; end_pos : position
  }

type 'a located =
  { it : 'a
  ; loc : span
  }

let mk loc it = { it; loc }

let merge_pos f pos1 pos2 =
  let new_file =
    match pos1.file, pos2.file with
    | Some f1, Some f2 when f1 = f2 -> Some f1
    | Some f, None | None, Some f -> Some f
    | _ -> None
  in
  let new_line = f pos1.line pos2.line in
  let new_col = f pos1.col pos2.col in
  { file = new_file; line = new_line; col = new_col }
;;

let merge_loc loc1 loc2 =
  { start_pos = merge_pos min loc1.start_pos loc2.start_pos
  ; end_pos = merge_pos max loc1.end_pos loc2.end_pos
  }
;;
