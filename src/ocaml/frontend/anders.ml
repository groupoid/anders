open Error

type cmdline =
  | Check     of string
  | Lex       of string
  | Parse     of string
  | Cubicaltt of string
  | Prim      of string * string
  | Repl | Help | Trace | Receive
  | Indices | Girard | Silent | Irrelevance

let help =
"\nhttps://homotopy.dev/library/

  invocation = anders | anders list
        list = [] | command list
   primitive = zero | one | interval

     command = check <filename>      | lex <filename>
             | parse <filename>      | prim primitive <name>
             | cubicaltt <filename>  | girard
             | trace                 | receive
             | indices               | silent
             | repl                  | help "

let repl = ref false
let cmd : cmdline -> unit = function
  | Check     filename -> Repl.check filename
  | Lex       filename -> Reader.lex filename
  | Parse     filename -> Reader.parse filename
  | Cubicaltt filename -> Cubical.extract filename
  | Prim (prim, value) -> begin match prim with
    | "zero"     -> Prefs.zeroPrim     := value
    | "one"      -> Prefs.onePrim      := value
    | "interval" -> Prefs.intervalPrim := value
    | _          -> raise (UnknownPrimitive prim)
  end
  | Repl         -> repl := true
  | Help         -> print_endline Repl.banner; print_endline help
  | Trace        -> Prefs.indices := true; Radio.set "trace" "true"
  | Receive      -> Radio.receive ()
  | Indices      -> Prefs.indices := true
  | Silent       -> Prefs.verbose := false
  | Girard       -> Radio.set "girard" "true"
  | Irrelevance  -> Radio.set "irrelevance" "true"

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "prim" :: prim :: value :: rest -> Prim (prim, value) :: parseArgs rest
  | "check"       :: filename :: rest -> Check     filename :: parseArgs rest
  | "lex"         :: filename :: rest -> Lex       filename :: parseArgs rest
  | "parse"       :: filename :: rest -> Parse     filename :: parseArgs rest
  | "cubicaltt"   :: filename :: rest -> Cubicaltt filename :: parseArgs rest
  | "help"        :: rest             -> Help        :: parseArgs rest
  | "trace"       :: rest             -> Trace       :: parseArgs rest
  | "receive"     :: rest             -> Receive     :: parseArgs rest
  | "indices"     :: rest             -> Indices     :: parseArgs rest
  | "silent"      :: rest             -> Silent      :: parseArgs rest
  | "girard"      :: rest             -> Girard      :: parseArgs rest
  | "irrelevance" :: rest             -> Irrelevance :: parseArgs rest
  | "repl"        :: rest             -> Repl        :: parseArgs rest
  | x :: xs -> Printf.printf "Unknown command “%s”\n" x; parseArgs xs

let defaults = function
  | [] -> [Help]
  | xs -> xs

let rec main () =
  try Array.to_list Sys.argv |> List.tl |> parseArgs |> defaults |> List.iter cmd;
    if !repl then Repl.repl () else ()
  with Restart -> Radio.wipe (); main ()

let () = main ()
