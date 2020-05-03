{
  open Parser
  open Lexing
}

let lat1   = ['a'-'z' 'A'-'Z' '0'-'9' '-' '_']
let ext1   = [^ '\t' ' ' '\r' '\n' '(' ')' ':' '.' ',' '/']
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']

let ch      = lat1|bytes2|bytes3|bytes4
let utf8    = ext1|bytes2|bytes3|bytes4
let ws      = ['\t' ' ' '\r' '\n']
let nl      = ['\r' '\n']
let comment = "--"  [^ '\n' '\r']* (nl|eof)
let colon   = ':'
let arrow   = "->"|"\xE2\x86\x92"
let defeq   = "="|":="|"\xE2\x89\x94"|"\xE2\x89\x9C"|"\xE2\x89\x9D"
let lam     = "\\"|"\xCE\xBB"
let star    = '*'

rule main = parse
| nl+             { SKIP }
| comment         { main lexbuf }
| ws+             { main lexbuf }
| "module"        { MODULE }
| "where"         { WHERE }
| "import"        { IMPORT }
| 'U'             { SET }
| ','             { COMMA }
| '_'             { HOLE }
| '('             { LPARENS }
| ')'             { RPARENS }
| '/'             { DIRSEP }
| ".1"            { FST }
| ".2"            { SND }
| "*"             { STAR }
| "?"             { HOLE }
| "undefined"     { UNDEF }
| defeq           { DEFEQ }
| lam             { LAM }
| arrow           { ARROW }
| colon           { COLON }
| ['0'-'9']+ as s { NAT (int_of_string s) }
| ch+ as s        { IDENT s }
| utf8+ as s      { OTHER s }
| eof             { EOF }