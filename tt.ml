open Expr
open Error
open Eval
open Check

type cmdline =
  | Check of string
  | Lex   of string
  | Parse of string
  | Repl
  | Help

let help =
"TT theorem prover

   invoke = tt | tt list
     list = [] | command list
  command = check filename | lex filename
          | parse filename | help"

let cmd : cmdline -> unit = function
  | Check filename -> Repl.check filename
  | Lex   filename -> Lexparse.lex filename
  | Parse filename -> Lexparse.parse filename
  | Help -> print_endline help
  | Repl -> Repl.repl ()

let needRepl : cmdline -> bool = function
  | Check _ -> true
  | _       -> false

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "check" :: filename :: rest -> Check filename :: parseArgs rest
  | "lex"   :: filename :: rest -> Lex   filename :: parseArgs rest
  | "parse" :: filename :: rest -> Parse filename :: parseArgs rest
  | "help"  :: rest -> Help :: parseArgs rest
  | x :: xs ->
    Printf.printf "Unknown command “%s”\n" x;
    parseArgs xs

let defaults : cmdline list -> cmdline list = function
  | [] -> [Help]
  | xs when List.exists needRepl xs -> xs @ [Repl]
  | xs -> xs

let () =
  while true do
    try Array.to_list Sys.argv |> List.tl
        |> parseArgs |> defaults |> List.iter cmd
    with Restart -> ()
  done