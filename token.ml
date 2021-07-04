open Parser

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT %s" s
  | PRE u      -> Printf.sprintf "PRE %d" u
  | KAN u      -> Printf.sprintf "KAN %d" u
  | DEF        -> "DEF"         | SIGMA      -> "SIGMA"
  | PI         -> "PI"          | HOLE       -> "HOLE"
  | RPARENS    -> "RPARENS"     | LPARENS    -> "LPARENS"
  | LAM        -> "LAM"         | PROD       -> "PROD"
  | OPTION     -> "OPTION"      | AXIOM      -> "AXIOM"
  | NO         -> "NO"          | EOF        -> "EOF"
  | FST        -> "FST"         | SND        -> "SND"
  | DEFEQ      -> "DEFEQ"       | COMMA      -> "COMMA"
  | COLON      -> "COLON"       | ARROW      -> "ARROW"
  | WHERE      -> "WHERE"       | MODULE     -> "MODULE"
  | IMPORT     -> "IMPORT"      | DIRSEP     -> "DIRSEP"
  | LT         -> "LT"          | GT         -> "GT"
  | APPFORMULA -> "APPFORMULA"  | NEGATE     -> "NEGATE"
  | AND        -> "AND"         | OR         -> "OR"
  | PATHP      -> "PATHP"       | TRANSP     -> "TRANSP"
  | ID         -> "ID"          | REF        -> "REF"