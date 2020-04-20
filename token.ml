open Parser

let tokenToString : token -> string = function
  | STAR -> "STAR"
  | SND -> "SND"
  | SKIP -> "SKIP"
  | SET -> "SET"
  | RPARENS -> "RPARENS"
  | LPARENS -> "LPARENS"
  | LAM -> "LAM"
  | IDENT s -> Printf.sprintf "IDENT %s" s
  | HOLE -> "HOLE"
  | FST -> "FST"
  | EOF -> "EOF"
  | DEFEQ -> "DEFEQ"
  | COMMA -> "COMMA"
  | COLON -> "COLON"
  | ARROW -> "ARROW"