open Error
open Expr

let checkMain filename rho gma e =
  Printf.printf "Parsed “%s” successfully.\n" filename;
  let rho = Check.check 1 rho gma e VSet in
  Printf.printf "File loaded.\n"; rho

let prettyPrintError : exn -> unit = function
  | TypeMismatch (u, v) ->
    Printf.printf "Type mismatch:\n%s\n  =/=\n%s\n"
                  (Expr.showValue u) (Expr.showValue v)
  | InferError e ->
    Printf.printf "Cannot infer type of\n  %s\n" (Expr.showExp e)
  | VariableNotFound p ->
    Printf.printf "Variable %s was not found\n" (Expr.showName p)
  | InvalidApplication (x, y) ->
    Printf.printf "Invalid application \n  %s\nto\n  %s\n"
                  (Expr.showValue x) (Expr.showValue y)
  | ExpectedPi x ->
    Printf.printf "  %s\nexpected to be Pi-type\n" (Expr.showValue x)
  | ExpectedSig x ->
    Printf.printf "  %s\nexpected to be Sigma-type\n" (Expr.showValue x)
  | UnknownCommand s ->
    Printf.printf "Unknown command “%s”\n" s
  | ex -> Printf.printf "uncaught exception: %s\n" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintError ex; default

let checkAndEval rho gma e : value * value =
  (Check.checkI 1 rho gma e, Eval.eval e rho)

let main rho gma : command -> unit = function
  | Eval e ->
    let (t, v) = checkAndEval rho gma e in
    Printf.printf "TYPE: %s\nEVAL: %s\n" (Expr.showValue t) (Expr.showValue v)
  | Command ("n", e) ->
    let (t0, v0) = checkAndEval rho gma e in
    let t = Eval.rbV 1 t0 in let v = Eval.rbV 1 v0 in
    Printf.printf "TYPE: %s\nNORMEVAL: %s\n" (Expr.showExp t) (Expr.showExp v)
  | Command (s, _) -> raise (UnknownCommand s)
  | Nope -> ()

let rho : rho ref   = ref Env.empty
let gma : gamma ref = ref Env.empty

let check filename =
  let chan = open_in filename in
  let exp = Parser.codecl Lexer.main (Lexing.from_channel chan) in
  close_in chan;
  let (rho', gma') =
    handleErrors (checkMain filename !rho !gma) exp
                 (!rho, !gma) in
  rho := rho'; gma := gma'

let repl () =
  try while true do
    print_string "> ";
    let line = read_line () in
    handleErrors (fun x ->
      let exp = Parser.repl Lexer.main (Lexing.from_string x) in
        main !rho !gma exp) line ()
  done with End_of_file -> ()  