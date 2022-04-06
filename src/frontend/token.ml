open Parser

let tokenToString : token -> string = function
  | IDENT s    -> Printf.sprintf "IDENT %s" s
  | PRE u      -> Printf.sprintf "PRE %s" (Z.to_string u)
  | KAN u      -> Printf.sprintf "KAN %s" (Z.to_string u)
  | EXT s      -> Printf.sprintf "EXT «%s»" s
  | DEF        -> "DEF"         | SIGMA      -> "SIGMA"
  | PI         -> "PI"          | HOLE       -> "HOLE"
  | RPARENS    -> "RPARENS"     | LPARENS    -> "LPARENS"
  | RSQ        -> "RSQ"         | LSQ        -> "LSQ"
  | LAM        -> "LAM"         | PROD       -> "PROD"
  | OPTION     -> "OPTION"      | AXIOM      -> "AXIOM"
  | IRREF      -> "IRREF"       | EOF        -> "EOF"
  | DEFEQ      -> "DEFEQ"       | COMMA      -> "COMMA"
  | COLON      -> "COLON"       | ARROW      -> "ARROW"
  | WHERE      -> "WHERE"       | MODULE     -> "MODULE"
  | LT         -> "LT"          | GT         -> "GT"
  | APPFORMULA -> "APPFORMULA"  | NEGATE     -> "NEGATE"
  | AND        -> "AND"         | OR         -> "OR"
  | PATHP      -> "PATHP"       | TRANSP     -> "TRANSP"
  | ID         -> "ID"          | REF        -> "REF"
  | PARTIAL    -> "PARTIAL"     | PARTIALP   -> "PARTIALP"
  | MAP        -> "MAP"         | IMPORT     -> "IMPORT"
  | INC        -> "INC"         | OUC        -> "OUC"
  | HCOMP      -> "HCOMP"       | DOT        -> "DOT"
  | IDJ        -> "IDJ"         | GLUE       -> "GLUE"
  | GLUEELEM   -> "GLUEELEM"    | UNGLUE     -> "UNGLUE"
  | W          -> "W"           | SUP        -> "SUP"
  | INDEMPTY   -> "INDEMPTY"    | INDUNIT    -> "INDUNIT"
  | INDBOOL    -> "INDBOOL"     | INDW       -> "W"
  | PLUGIN     -> "PLUGIN"      | IM         -> "IM"
  | INF        -> "INF"         | INDIM      -> "INDIM"
  | JOIN       -> "JOIN"
