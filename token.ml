open Parser

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT %s" s
  | SET u      -> Printf.sprintf "SET %d" u
  | DEF        -> "DEF"         | SIGMA      -> "SIGMA"
  | PI         -> "PI"          | SND        -> "SND"
  | RPARENS    -> "RPARENS"     | LPARENS    -> "LPARENS"
  | LAM        -> "LAM"         | OPTION     -> "OPTION"
  | HOLE       -> "HOLE"        | AXIOM      -> "AXIOM"
  | NO         -> "NO"          | FST        -> "FST"
  | EOF        -> "EOF"         | DEFEQ      -> "DEFEQ"
  | COMMA      -> "COMMA"       | COLON      -> "COLON"
  | ARROW      -> "ARROW"       | WHERE      -> "WHERE"
  | MODULE     -> "MODULE"      | IMPORT     -> "IMPORT"
  | LT         -> "LT"          | GT         -> "GT"
  | PATHP      -> "PATHP"       | APPFORMULA -> "APPFORMULA"
  | ZERO       -> "ZERO"        | ONE        -> "ONE"
  | NEGATE     -> "NEGATE"      | AND        -> "AND"
  | OR         -> "OR"          | DIRSEP     -> "DIRSEP"
