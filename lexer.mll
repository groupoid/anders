{
  open Parser
  open Lexing
}

let ch     = ['a'-'z' 'A'-'Z' '0'-'9']
let ws     = (['\t' ' ' '\r' '\n']|"--"_*)
let colon  = ':'
let arrow  = "->"
let defeq  = ":="
let lam    = "\\"|"\xCE\xBB"
let star   = '*'
let pi     = "forall"|"\xCE\xA0"
let sigma  = "sigma"|"\xCE\xA3"

rule main = parse
| ws+      { main lexbuf }
| "U"      { SET }
| ','      { COMMA }
| '_'      { HOLE }
| '('      { LPARENS }
| ')'      { RPARENS }
| ".1"     { FST }
| ".2"     { SND }
| defeq    { DEFEQ }
| lam      { LAM }
| arrow    { ARROW }
| colon    { COLON }
| "def"    { DEF }
| pi       { PI }
| sigma    { SIGMA }
| ch+ as s { IDENT s }
| eof      { EOF }