{
  open Parser
  open Lexing

  let next_line lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1 }
}

let lat1   = ['a'-'z' 'A'-'Z' '0'-'9' '-' '_']
let ext1   = [^ '\t' ' ' '\r' '\n' '(' ')' ':' '.' ',' '/']
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']

let ch      = lat1|bytes2|bytes3|bytes4
let utf8    = ext1|bytes2|bytes3|bytes4
let ws      = ['\t' ' ']
let nl      = "\r\n"|"\r"|"\n"
let comment = "--" [^ '\n' '\r']* (nl|eof)
let colon   = ':'
(* arrow := -> | →
   defeq := := | ≔ | ≜ | ≝
   lam   := \  | λ *)
let arrow   = "->"|"\xE2\x86\x92"
let defeq   = ":="|"\xE2\x89\x94"|"\xE2\x89\x9C"|"\xE2\x89\x9D"
let lam     = "\\"|"\xCE\xBB"
let pi      = "pi"|"\xCE\xA0"
let sigma   = "sigma"|"\xCE\xA3"
let def     = "def"|"definition"|"theorem"|"lemma"|"corollary"|"proposition"
let axiom   = "axiom"|"postulate"

rule main = parse
| nl              { next_line lexbuf; main lexbuf }
| comment         { next_line lexbuf; main lexbuf }
| ws+             { main lexbuf }
| "module"        { MODULE }
| "where"         { WHERE }
| "import"        { IMPORT }
| "option"        { OPTION }
| def             { DEF }
| 'U'             { SET }
| ','             { COMMA }
| '_'             { NO }
| '('             { LPARENS }
| ')'             { RPARENS }
| '/'             { DIRSEP }
| ".1"            { FST }
| ".2"            { SND }
| pi              { PI }
| sigma           { SIGMA }
| "?"             { HOLE }
| axiom           { AXIOM }
| defeq           { DEFEQ }
| lam             { LAM }
| arrow           { ARROW }
| colon           { COLON }
| ['0'-'9']+ as s { NAT (int_of_string s) }
| utf8+ as s      { IDENT s }
| eof             { EOF }