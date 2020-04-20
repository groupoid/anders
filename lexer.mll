{
  open Parser
  open Lexing
}

let bytes1 = ['a'-'z' 'A'-'Z' '0'-'9' '-' '_']
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']

let ch     = bytes1|bytes2|bytes3|bytes4
let ws     = (['\t' ' ' '\r' '\n']|"--"_*)
let nl     = ['\r' '\n']
let colon  = ':'
let arrow  = "->"|"\xE2\x86\x92"
let defeq  = "="|":="|"\xE2\x89\x94"|"\xE2\x89\x9C"|"\xE2\x89\x9D"
let lam    = "\\"|"\xCE\xBB"
let star   = '*'

rule main = parse
| nl+      { SKIP }
| ws+      { main lexbuf }
| "U"      { SET }
| ','      { COMMA }
| '_'      { HOLE }
| '('      { LPARENS }
| ')'      { RPARENS }
| ".1"     { FST }
| ".2"     { SND }
| "*"      { STAR }
| defeq    { DEFEQ }
| lam      { LAM }
| arrow    { ARROW }
| colon    { COLON }
| ch+ as s { IDENT s }
| eof      { EOF }