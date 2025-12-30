open Error
module I = Parser.MenhirInterpreter

let get_parse_error env =
  match I.stack env with
  | (lazy Nil) -> "Invalid syntax"
  | (lazy (Cons (I.Element (state, _, _, _), _))) ->
    (try ParserMessages.message (I.number state) with
     | Not_found -> "invalid syntax (no specific message for this error)")
;;

let rec parse lexbuf (checkpoint : 'a I.checkpoint) : 'a =
  match checkpoint with
  | I.InputNeeded _env ->
    let token = Lexer.token lexbuf in
    let startp = lexbuf.lex_start_p
    and endp = lexbuf.lex_curr_p in
    let checkpoint = I.offer checkpoint (token, startp, endp) in
    parse lexbuf checkpoint
  | I.Shifting _ | I.AboutToReduce _ ->
    let checkpoint = I.resume checkpoint in
    parse lexbuf checkpoint
  | I.HandlingError env ->
    let position = Some (Utils.get_lexing_position lexbuf) in
    let message = get_parse_error env in
    raise (Syntax_error { position; message })
  | I.Accepted v -> v
  | I.Rejected -> raise (Syntax_error { position = None; message = "Parsing rejected" })
;;
