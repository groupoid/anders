open Parser

let tokenToString : token -> string = function
  | IDENT s -> Printf.sprintf "IDENT %s" s
  | OTHER s -> Printf.sprintf "OTHER %s" s
  | STAR    -> "STAR"
  | SND     -> "SND"
  | SKIP    -> "SKIP"
  | SET     -> "SET"
  | RPARENS -> "RPARENS"
  | LPARENS -> "LPARENS"
  | LAM     -> "LAM"
  | HOLE    -> "HOLE"
  | FST     -> "FST"
  | EOF     -> "EOF"
  | DEFEQ   -> "DEFEQ"
  | COMMA   -> "COMMA"
  | COLON   -> "COLON"
  | ARROW   -> "ARROW"