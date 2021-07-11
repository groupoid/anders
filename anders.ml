open Error
open Ident

type cmdline =
  | Check     of string
  | Lex       of string
  | Parse     of string
  | Cubicaltt of string
  | Prim      of string * string
  | Repl  | Help
  | Trace | Girard  | Verbose

let help =
"  invocation = anders | anders list
        list = [] | command list
   primitive = zero | one | interval | ...

     command = check <filename>      | lex <filename>
             | parse <filename>      | prim primitive <name>
             | cubicaltt <filename>  | girard
             | trace                 | verbose
             | repl                  | help "

let repl = ref false
let cmd : cmdline -> unit = function
  | Check     filename -> Repl.check filename
  | Lex       filename -> Reader.lex filename
  | Parse     filename -> Reader.parse filename
  | Cubicaltt filename -> Cubical.extract filename
  | Prim (prim, value) -> begin match prim with
    | "zero"     -> zeroPrim     := value
    | "one"      -> onePrim      := value
    | "interval" -> intervalPrim := value
    | _ -> raise (UnknownPrimitive prim)
  end
  | Help -> print_endline (Repl.banner ^ "\n"); print_endline help
  | Repl -> repl := true
  | Verbose -> Ident.verbose := true
  | Trace -> Ident.trace := true
  | Girard -> girard := true

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "prim" :: prim :: value :: rest -> Prim (prim, value) :: parseArgs rest
  | "check"     :: filename :: rest -> Check     filename :: parseArgs rest
  | "lex"       :: filename :: rest -> Lex       filename :: parseArgs rest
  | "parse"     :: filename :: rest -> Parse     filename :: parseArgs rest
  | "cubicaltt" :: filename :: rest -> Cubicaltt filename :: parseArgs rest
  | "help"      :: rest             -> Help    :: parseArgs rest
  | "trace"     :: rest             -> Trace   :: parseArgs rest
  | "verbose"   :: rest             -> Verbose :: parseArgs rest
  | "girard"    :: rest             -> Girard  :: parseArgs rest
  | "repl"      :: rest             -> Repl    :: parseArgs rest
  | x :: xs -> Printf.printf "Unknown command “%s”\n" x; parseArgs xs

let defaults = function
  | [] -> [Help]
  | xs -> xs

let rec main () =
  try Array.to_list Sys.argv |> List.tl |> parseArgs |> defaults |> List.iter cmd;
    if !repl then Repl.repl () else ()
  with Restart -> main ()

let () = main ()
