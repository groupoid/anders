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
  let exp = Parser.codecl Lexer.main (Lexing.from_channel chan) in
  print_endline (Expr.showExp exp)