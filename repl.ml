open Error
open Expr

let help =
"Available commands:
  <statement> Infer type and evaluate statement
  :n          <statement> normalize statement
  :q          Quit
  :r          Restart
  :h          Display this message"

let init : Decl.state = (Env.empty, Env.empty, Files.empty)
let st : Decl.state ref = ref init

let checkAndEval rho gma e : value * value =
  (Check.infer rho gma e, Eval.eval e rho)

let main rho gma : command -> unit = function
  | Eval e ->
    let (t, v) = checkAndEval rho gma e in
    Printf.printf "TYPE: %s\nEVAL: %s\n" (Expr.showValue t) (Expr.showValue v)
  | Command ("n", e) ->
    let (t0, v0) = checkAndEval rho gma e in
    let t = Eval.rbV t0 in let v = Eval.rbV v0 in
    Printf.printf "TYPE: %s\nNORMEVAL: %s\n" (Expr.showExp t) (Expr.showExp v)
  | Action "q" -> exit 0
  | Action "r" -> st := init; raise Restart
  | Action "h" -> print_endline help
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let check filename =
  st := handleErrors (Decl.checkFile !st) filename !st

let repl () =
  let (rho, gma, _) = !st in
  try while true do
    print_string "> ";
    let line = read_line () in
    handleErrors (fun x ->
      let exp = Lexparse.parseErr Parser.repl
                  (Lexing.from_string x) in
      main rho gma exp) line ()
  done with End_of_file -> ()