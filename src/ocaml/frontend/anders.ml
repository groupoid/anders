open Error

type cmdline =
  | Check     of string
  | Lex       of string
  | Parse     of string
  | Prim      of string * string
  | Repl | Help | Trace | Receive | Preeval
  | Indices | Girard | Silent | Irrelevance

let help =
"\nhttps://homotopy.dev/library/

  invocation = anders | anders list
        list = [] | command list

     command = check <filename>      | lex <filename>
             | parse <filename>      | girard
             | trace                 | receive
             | indices               | silent
             | preeval               | irrelevance
             | repl                  | help "

let cmd : cmdline -> unit = function
  | Check     filename -> Repl.check filename
  | Lex       filename -> Reader.lex filename
  | Parse     filename -> Reader.parse filename
  | Repl         -> Prefs.repl := true
  | Help         -> print_endline Repl.banner; print_endline help
  | Trace        -> Prefs.indices := true; Radio.set "trace" "true"
  | Receive      -> Radio.receive ()
  | Indices      -> Prefs.indices := true
  | Silent       -> Prefs.verbose := false
  | Preeval      -> Radio.set "preeval" "true"
  | Girard       -> Radio.set "girard" "true"
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
  | "indices"     :: rest             -> Indices     :: parseArgs rest
  | "irrelevance" :: rest             -> Irrelevance :: parseArgs rest
  | "receive"     :: rest             -> Receive     :: parseArgs rest
  | x :: xs -> Printf.printf "Unknown command “%s”\n" x; parseArgs xs

let defaults = function
  | [] -> [Help]
  | xs -> xs

let rec main () =
  try Array.to_list Sys.argv |> List.tl |> parseArgs |> defaults |> List.iter cmd;
    if !Prefs.repl then Repl.repl () else ()
  with Restart -> Radio.wipe (); main ()

let () = main ()
