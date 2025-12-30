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
