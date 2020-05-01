open Error
open Expr

let checkMain rho gma filename =
  let chan = open_in filename in
  let exp = Lexparse.parseErr Parser.codecl (Lexing.from_channel chan) in
  close_in chan; Printf.printf "Parsed “%s” successfully.\n" filename;
  let rho = Check.check 1 rho gma exp (VSet 1) in
  Printf.printf "File loaded.\n"; rho

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
  | Command (s, _) | Action s -> raise (UnknownCommand s)
  | Nope -> ()

let rho : rho ref   = ref Env.empty
let gma : gamma ref = ref Env.empty

let check filename =
  let (rho', gma') = handleErrors (checkMain !rho !gma) filename (!rho, !gma) in
  rho := rho'; gma := gma'

let repl () =
  try while true do
    print_string "> ";
    let line = read_line () in
    handleErrors (fun x ->
      let exp = Lexparse.parseErr Parser.repl
        (Lexing.from_string x) in
          main !rho !gma exp) line ()
  done with End_of_file -> ()  