open Parser

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT %s" s
  | NAT u      -> Printf.sprintf "NAT %d" u
  | DEF        -> "DEF"         | SIGMA      -> "SIGMA"
  | PI         -> "PI"          | SND        -> "SND"
  | SET        -> "SET"         | RPARENS    -> "RPARENS"
  | LPARENS    -> "LPARENS"     | LAM        -> "LAM"
  | HOLE       -> "HOLE"        | AXIOM      -> "AXIOM"
  | NO         -> "NO"          | FST        -> "FST"
  | EOF        -> "EOF"         | DEFEQ      -> "DEFEQ"
  | COMMA      -> "COMMA"       | COLON      -> "COLON"
  | ARROW      -> "ARROW"       | WHERE      -> "WHERE"
  | MODULE     -> "MODULE"      | IMPORT     -> "IMPORT"
  | DIRSEP     -> "DIRSEP"      | OPTION     -> "OPTION"
  | LT         -> "LT"          | GT         -> "GT"
  | PATHP      -> "PATHP"       | APPFORMULA -> "APPFORMULA"
  | ZERO       -> "ZERO"        | ONE        -> "ONE"
  | NEGATE     -> "NEGATE"      | AND        -> "AND"
  | OR         -> "OR"
