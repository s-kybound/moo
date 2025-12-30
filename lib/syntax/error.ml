open Loc

exception
  Syntax_error of
    { position : position option
    ; message : string
    }
