open Error
open Expr

let init : Decl.state = (Env.empty, Env.empty, Files.empty)
let st : Decl.state ref = ref init

let checkAndEval rho gma e : value * value =
  (Check.infer 1 rho gma e, Eval.eval e rho)

let main rho gma : command -> unit = function
  | Eval e ->
    let (t, v) = checkAndEval rho gma e in
    Printf.printf "TYPE: %s\nEVAL: %s\n" (Expr.showValue t) (Expr.showValue v)
  | Command ("n", e) ->
    let (t0, v0) = checkAndEval rho gma e in
    let t = Eval.rbV 1 t0 in let v = Eval.rbV 1 v0 in
    Printf.printf "TYPE: %s\nNORMEVAL: %s\n" (Expr.showExp t) (Expr.showExp v)
  | Action "q" -> exit 0
  | Action "r" -> st := init; raise Restart
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