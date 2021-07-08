open Error
open Ident
open Decl
open Expr

let help =
"Available commands:
  <statement>    infer type and evaluate statement
  :n <statement> normalize statement
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
  | Command ("n", e) -> let (t0, v0) = checkAndEval ctx (freshExp e) in
    let t = Check.rbV t0 in let v = Check.rbV v0 in
    Printf.printf "TYPE: %s\nNORMEVAL: %s\n" (showExp t) (showExp v)
  | Action "q" -> exit 0
  | Action "r" -> st := init; raise Restart
  | Action "h" -> print_endline help
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let check filename =
  st := handleErrors (checkFile !st) filename !st

let repl () =
  let (ctx, _) = !st in
  try while true do
    print_string "> ";
    let line = read_line () in
    handleErrors (fun x ->
      let cmd = Lexparse.parseErr Parser.repl
                  (Lexing.from_string x) in
      main ctx cmd) line ()
  done with End_of_file -> ()