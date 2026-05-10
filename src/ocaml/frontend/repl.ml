open Prettyprinter
open Module
open Error
open Decl

open Radio

let help =
"Available commands:
  <statement>    infer type and normalize statement
  :q             quit
  :r             restart
  :save <file>   save term to file <file>.bin
  :load <file>   load term from file <file>.bin
  :h             display this message

Information about shell commands can be found at ‘:h’."

let banner =
  Printf.sprintf "Anders Proof Assistant version %Ld.%Ld.%Ld
Copyright © 2016–2026 Groupoid Infinity." 5L 5L 0L

let loaded : Files.t ref = ref Files.empty

let main : command -> unit = function
  | Eval e | Norm e | Command ("norm", e) ->
    let (t, v) = (infer e, eval e) in
    Printf.printf "TYPE: %s\nNORM: %s\n" (showExp t) (showExp v)
  | Save (f, e) | Command ("save", EApp (EVar (Ident (f, _)), e)) ->
    save (f ^ ".bin") f e; Printf.printf "Saved to %s.bin\n" f
  | Command ("save", e) ->
    let f = match e with EVar (Ident (x, _)) -> x | _ -> "term" in
    save (f ^ ".bin") f e; Printf.printf "Saved to %s.bin\n" f
  | Load f | Command ("load", EVar (Ident (f, _))) ->
    let (e, t) = load (f ^ ".bin") in
    Printf.printf "LOADED %s FROM %s.bin\nTYPE: %s\nNORM: %s\n" f f (showExp t) (showExp e)
  | Action "q" -> exit 0
  | Action "r" -> loaded := Files.empty; raise Restart
  | Action "h" -> print_endline help
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let check filename = loaded := handleErrors (checkFile !loaded) filename !loaded

let repl () =
  print_endline (banner ^ "\n\nFor help type ‘:h’.\n");
  try while true do
    print_string "> "; let line = read_line () in
    handleErrors (fun x -> main (Reader.parseErr Parser.repl
      (Lexing.from_string x) "<stdin>")) line ()
  done with End_of_file -> ()
