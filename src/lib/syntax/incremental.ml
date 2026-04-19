open Error
module I = Parser.MenhirInterpreter

let expected_tokens_of_checkpoint k =
  let foo = Token.tokens in
  List.filter (fun x -> I.acceptable k x Lexing.dummy_pos) foo
;;

let rec parse_module_aux
          lexbuf
          (previous_input_needed : (Parser.token * Surface.module_ I.checkpoint) option)
          (checkpoint : 'a I.checkpoint)
  : Surface.module_
  =
  match checkpoint with
  | I.Accepted v -> v
  | I.Rejected -> raise (SyntaxError { span = None; message = "Parsing rejected" })
  | I.InputNeeded _env ->
    let token = Lexer.token lexbuf in
    let startp = lexbuf.lex_start_p
    and endp = lexbuf.lex_curr_p in
    let new_checkpoint = I.offer checkpoint (token, startp, endp) in
    parse_module_aux lexbuf (Some (token, checkpoint)) new_checkpoint
  | I.Shifting _ | I.AboutToReduce _ ->
    let checkpoint = I.resume checkpoint in
    parse_module_aux lexbuf previous_input_needed checkpoint
  | I.HandlingError _ ->
    let span = Some (Loc_utils.get_lexing_span lexbuf) in
    let resume_pos = lexbuf.lex_curr_p in
    (match previous_input_needed with
     | Some (Parser.EOF, k) -> raise (Early_eof (k, resume_pos))
     | Some (tok, k) ->
       let expecteds =
         expected_tokens_of_checkpoint k
         |> List.map Token.string_of_token
         |> List.sort_uniq String.compare
       in
       let got = Token.string_of_token tok in
       let message =
         match expecteds with
         | [] -> "unexpected token " ^ got
         | [ expected ] -> Printf.sprintf "expected %s, got %s" expected got
         | _ ->
           Printf.sprintf
             "expected one of %s, got %s"
             (String.concat ", " expecteds)
             got
       in
       raise (SyntaxError { span; message })
     | None -> raise (SyntaxError { span; message = "unknown syntax error" }))
;;

let parse_module (lexbuf : Lexing.lexbuf) =
  let initial_checkpoint = Parser.Incremental.parse_program lexbuf.lex_curr_p in
  parse_module_aux lexbuf None initial_checkpoint
;;

let resume_parse_module lexbuf (k : Surface.module_ I.checkpoint) =
  parse_module_aux lexbuf None k
;;
