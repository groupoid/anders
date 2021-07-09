{
  open Parser
  open Lexing

  let nextLine lexbuf =
    let pos = lexbuf.lex_curr_p in
    lexbuf.lex_curr_p <-
      { pos with pos_bol = pos.pos_cnum;
                 pos_lnum = pos.pos_lnum + 1 }

  let getLevel s =
    let res = ref 0 in let queue = Queue.of_seq (String.to_seq s) in
    let sym = Queue.take queue in if (sym <> 'U' && sym <> 'V') then
      failwith "invalid universe";

    while not (Queue.is_empty queue) do
      if (Queue.take queue <> '\xE2' ||
          Queue.take queue <> '\x82')
      then failwith "invalid universe level while lexing";

      let value = Char.code (Queue.take queue) - 0x80 in
      res := !res * 10 + value
    done; !res
}

let lat1   = [^ '\t' ' ' '\r' '\n' '(' ')' '[' ']' ':' '.' ',' '<' '>']
let beg    = lat1 # '-'
let bytes2 = ['\192'-'\223']['\128'-'\191']
let bytes3 = ['\224'-'\239']['\128'-'\191']['\128'-'\191']
let bytes4 = ['\240'-'\247']['\128'-'\191']['\128'-'\191']['\128'-'\191']

let nl               = "\r\n"|"\r"|"\n"
let inlineComment    = "--" [^ '\n' '\r']* (nl|eof)
let multilineComment = "{-" [^ '-']* '-' ([^ '-' '}'][^ '-']* '-' | '-')* '}'
let comment          = inlineComment | multilineComment

let utf8    = lat1|bytes2|bytes3|bytes4
let ident   = beg utf8*
let ws      = ['\t' ' ']
let colon   = ':'
let defeq   = ":="     | "\xE2\x89\x94" | "\xE2\x89\x9C" | "\xE2\x89\x9D" (* ≔ | ≜ | ≝ *)
let arrow   = "->"     | "\xE2\x86\x92" (* → *)
let prod    = "*"      | "\xC3\x97"     (* × *)
let lam     = "\\"     | "\xCE\xBB"     (* λ *)
let pi      = "forall" | "\xCE\xA0"     (* Π *)
let sigma   = "sigma"  | "\xCE\xA3"     (* Σ *)
let map     = "|->"    | "\xE2\x86\xA6" (* ↦ *)
let def     = "definition" | "def" | "theorem" | "lemma" | "corollary" | "proposition"
let axiom   = "axiom"|"postulate"

let negFormula = "-"
let andFormula = "/\\"|"\xE2\x88\xA7" (* ∧ *)
let orFormula  = "\\/"|"\xE2\x88\xA8" (* ∨ *)

let subscript = '\xE2' '\x82' ['\x80'-'\x89']
let kan       = 'U' subscript*
let pre       = 'V' subscript*

rule main = parse
| nl              { nextLine lexbuf; main lexbuf }
| comment         { nextLine lexbuf; main lexbuf }
| ws+             { main lexbuf }
| "module"        { MODULE }           | "where"         { WHERE }
| "import"        { IMPORT }           | "option"        { OPTION }
| def             { DEF }              | colon           { COLON }
| ','             { COMMA }            | '_'             { IRREF }
| '('             { LPARENS }          | ')'             { RPARENS }
| '['             { LSQ }              | ']'             { RSQ }
| ".1"            { FST }              | ".2"            { SND }
| pi              { PI }               | sigma           { SIGMA }
| "<"             { LT }               | ">"             { GT }
| negFormula      { NEGATE }           | andFormula      { AND }
| orFormula       { OR }               | "@"             { APPFORMULA }
| axiom           { AXIOM }            | defeq           { DEFEQ }
| lam             { LAM }              | arrow           { ARROW }
| prod            { PROD }             | kan as s        { KAN (getLevel s) }
| "PathP"         { PATHP }            | "transp"        { TRANSP }
| "Id"            { ID }               | "ref"           { REF }
| "idJ"           { IDJ }              | pre as s        { PRE (getLevel s) }
| "?"             { HOLE }             | "Partial"       { PARTIAL }
| map             { MAP }              | ident as s      { IDENT s }
| eof             { EOF }
