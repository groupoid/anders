open Error

type cmdline =
  | Check     of string
  | Lex       of string
  | Parse     of string
  | Prim      of string * string
  | Repl | Help | Trace | Receive | Preeval
  | Indices | Girard | Silent | Irrelevance

let help =
"
 Home: https://homotopy.dev/
 Use:

    exec := anders | anders list
    list := []     | comm list
    comm := check <filename> | silent
          | parse <filename> | trace
          | lex <filename>   | girard
          | preeval          | irrelevance
          | repl             | help
"

let cmd : cmdline -> unit = function
  | Check     filename -> Repl.check filename
  | Lex       filename -> Reader.lex filename
  | Parse     filename -> Reader.parse filename
  | Repl         -> Prefs.repl := true
  | Help         -> print_endline Repl.banner; print_endline help
  | Trace        -> Prefs.indices := true; Radio.set "trace" "true"
  | Receive      -> Radio.receive ()
  | Silent       -> Prefs.verbose := false
  | Preeval      -> Radio.set "preeval"     "true"
  | Girard       -> Radio.set "girard"      "true"
  | Irrelevance  -> Radio.set "irrelevance" "true"

let rec parseArgs : string list -> cmdline list = function
  | [] -> []
  | "check"       :: filename :: rest -> Check     filename :: parseArgs rest
  | "lex"         :: filename :: rest -> Lex       filename :: parseArgs rest
  | "parse"       :: filename :: rest -> Parse     filename :: parseArgs rest
  | "girard"      :: rest             -> Girard      :: parseArgs rest
  | "repl"        :: rest             -> Repl        :: parseArgs rest
  | "help"        :: rest             -> Help        :: parseArgs rest
  | "trace"       :: rest             -> Trace       :: parseArgs rest
  | "preeval"     :: rest             -> Preeval     :: parseArgs rest
  | "silent"      :: rest             -> Silent      :: parseArgs rest
  | "irrelevance" :: rest             -> Irrelevance :: parseArgs rest
  | x :: xs -> Printf.printf "Unknown command “%s”\n" x; parseArgs xs

let defaults = function
  | [] -> [Help]
  | xs -> xs

let rec main () =
  try Array.to_list Sys.argv |> List.tl |> parseArgs |> defaults |> List.iter cmd;
    if !Prefs.repl then Repl.repl () else ()
  with Restart -> Radio.wipe (); main ()

let () = main ()
