open Error
module I = Parser.MenhirInterpreter

let get_parse_error env =
  match I.stack env with
  | (lazy Nil) -> "Invalid syntax"
  | (lazy (Cons (I.Element (state, _, _, _), _))) ->
  try ParserMessages.message (I.number state) with
  | Not_found -> "invalid syntax (no specific message for this error)"
;;

let rec parse_module_aux
          lexbuf
          (previous : (Parser.token * Surface.module_ I.checkpoint) option)
          (checkpoint : 'a I.checkpoint)
  : Surface.module_
  =
  match checkpoint with
  | I.Accepted v -> v
  | I.Rejected -> raise (Syntax_error { span = None; message = "Parsing rejected" })
  | I.InputNeeded _env ->
    let token = Lexer.token lexbuf in
    let startp = lexbuf.lex_start_p
    and endp = lexbuf.lex_curr_p in
    let new_checkpoint = I.offer checkpoint (token, startp, endp) in
    parse_module_aux lexbuf (Some (token, checkpoint)) new_checkpoint
  | I.Shifting _ | I.AboutToReduce _ ->
    let checkpoint = I.resume checkpoint in
    parse_module_aux lexbuf previous checkpoint
  | I.HandlingError env ->
    let span = Some (Utils.get_lexing_span lexbuf) in
    let resume_pos = lexbuf.lex_curr_p in
    let message = get_parse_error env in
    (match previous with
     | Some (Parser.EOF, k) -> raise (Early_eof (k, resume_pos))
     | _ -> raise (Syntax_error { span; message }))
;;

let parse_module (lexbuf : Lexing.lexbuf) =
  let initial_checkpoint = Parser.Incremental.parse_program lexbuf.lex_curr_p in
  parse_module_aux lexbuf None initial_checkpoint
;;

let resume_parse_module lexbuf (k : Surface.module_ I.checkpoint) =
  parse_module_aux lexbuf None k
;;
