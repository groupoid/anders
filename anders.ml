open Prefs
open Check
open Error
open Ident
open Expr

type cmdline =
  | Check     of string
  | Lex       of string
  | Parse     of string
  | Cubicaltt of string
  | Prim      of string * string
  | Repl  | Help
  | Trace | Girard

let banner = "Anders theorem prover [MLTT].\n"
let help =
"    invoke = anders | anders list
      list = [] | command list
   command = check filename      | lex filename
           | parse filename      | help
           | cubicaltt filename  | girard
           | prim primitive name | trace
 primitive = zero | one | interval"

let cmd : cmdline -> unit = function
  | Check     filename -> Repl.check filename
  | Lex       filename -> Lexparse.lex filename
  | Parse     filename -> Lexparse.parse filename
  | Cubicaltt filename -> Cubical.extract filename
  | Prim (prim, value) -> begin match prim with
    | "zero"     -> zeroPrim     := value
    | "one"      -> onePrim      := value
    | "interval" -> intervalPrim := value
    | _ -> raise (UnknownPrimitive prim)
  end
  | Help -> print_endline help
  | Repl -> Repl.repl ()
  | Trace -> Prefs.trace := true
  | Girard -> girard := true

let needRepl : cmdline -> bool = function
  | Check _ -> true
  | _       -> false

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "prim" :: prim :: value :: rest -> Prim (prim, value) :: parseArgs rest
  | "check"     :: filename :: rest -> Check     filename :: parseArgs rest
  | "lex"       :: filename :: rest -> Lex       filename :: parseArgs rest
  | "parse"     :: filename :: rest -> Parse     filename :: parseArgs rest
  | "cubicaltt" :: filename :: rest -> Cubicaltt filename :: parseArgs rest
  | "help"      :: rest             -> Help :: parseArgs rest
  | "trace"     :: rest             -> Trace :: parseArgs rest
  | "girard"    :: rest             -> Girard :: parseArgs rest
  | x :: xs ->
    Printf.printf "Unknown command “%s”\n" x;
    parseArgs xs

let defaults : cmdline list -> cmdline list = function
  | [] -> [Help]
  | xs when List.exists needRepl xs -> xs @ [Repl]
  | xs -> xs

let rec main () =
  try Array.to_list Sys.argv |> List.tl |> parseArgs |> defaults |> List.iter cmd
  with Restart -> main ()

let () = print_endline banner; main ()