open Loc
module I = Parser.MenhirInterpreter

type kont = Surface.module_ I.checkpoint * Lexing.position

exception
  SyntaxError of
    { span : span option
    ; message : string
    }

exception
  TypeError of
    { loc : span option
    ; message : string
    }

exception Early_eof of kont
