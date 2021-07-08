open Lexing

let parseErr f lexbuf =
  try f Lexer.main lexbuf
  with Parser.Error ->
    raise (Error.Parser (lexbuf.lex_curr_p.pos_lnum, lexeme lexbuf))

let lex filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  Printf.printf "Lexing “%s”.\n" filename;
  try while true do
    let tok = Lexer.main lexbuf in
    if tok = Parser.EOF then raise End_of_file
    else print_string (Token.tokenToString tok ^ " ")
  done with End_of_file -> close_in chan;
  print_newline ()

let parse filename =
  let chan = open_in filename in
  Printf.printf "Parsing “%s”.\n" filename;
  Error.handleErrors
    (fun chan ->
      let lexbuf = Lexing.from_channel chan in
      let file = parseErr Parser.file lexbuf in
      print_endline (Module.showFile file))
    chan ()