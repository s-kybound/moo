open Loc
module I = Parser.MenhirInterpreter

type kont = Surface.module_ I.checkpoint * Lexing.position

exception
  Syntax_error of
    { span : span option
    ; message : string
    }

exception Early_eof of kont
