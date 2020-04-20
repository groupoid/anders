open Expr
open Error
open Eval
open Check

type cmdline =
  | Check of string
  | Lex   of string
  | Repl
  | Help

let lex filename =
  let chan = open_in filename in
  let lexbuf = Lexing.from_channel chan in
  Printf.printf "Lexing “%s”.\n" filename;
  try while true do
    let tok = Lexer.main lexbuf in
    if tok = Parser.EOF then raise End_of_file
    else print_string (Token.tokenToString tok ^ " ")
  done with End_of_file -> close_in chan;
  print_string "\n"

let help =
"TT theorem prover

   invoke = tt | tt list
     list = [] | command list
  command = check filename | lex filename | help"

let cmd : cmdline -> unit = function
  | Check filename -> Repl.check filename
  | Lex   filename -> lex filename
  | Help -> print_endline help
  | Repl -> Repl.repl ()

let needRepl : cmdline -> bool = function
  | Check _ -> true
  | _       -> false

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "check" :: filename :: rest -> Check filename :: parseArgs rest
  | "lex"   :: filename :: rest -> Lex   filename :: parseArgs rest
  | "help"  :: rest -> Help :: parseArgs rest
  | x :: xs ->
    Printf.printf "Unknown command “%s”\n" x;
    parseArgs xs

let defaults : cmdline list -> cmdline list = function
  | [] -> [Help]
  | xs when List.exists needRepl xs -> xs @ [Repl]
  | xs -> xs

let _ =
  Array.to_list Sys.argv |> List.tl
  |> parseArgs |> defaults |> List.iter cmd