open Prettyprinter
open Module
open Error
open Decl
open Elab
open Expr

let help =
"Available commands:
  <statement>    infer type and normalize statement
  :q             quit
  :r             restart
  :h             display this message"

let init : state = empty
let st : state ref = ref init

let checkAndEval ctx e : value * value =
  (Check.infer ctx e, Check.eval e ctx)

let main ctx : command -> unit = function
  | Eval e -> let (t, v) = checkAndEval ctx (freshExp e) in
    Printf.printf "TYPE: %s\nEVAL: %s\n" (showValue t) (showValue v)
  | Action "q" -> exit 0
  | Action "r" -> st := init; raise Restart
  | Action "h" -> print_endline help
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let check filename =
  st := handleErrors (checkFile !st) filename !st

let banner = "Anders theorem prover [MLTT][CCHM][HTS] version 0.7.2"

let repl () =
  print_endline ("\n" ^ banner) ;
  let (ctx, _) = !st in
  try while true do
    print_string "> ";
    let line = read_line () in
    handleErrors (fun x ->
      let cmd = Reader.parseErr Parser.repl (Lexing.from_string x) "<stdin>" in
        main ctx cmd) line ()
  done with End_of_file -> ()