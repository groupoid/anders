open Expr
open Error
open Eval
open Check

let checkMain filename rho gma e =
  Printf.printf "Parsed “%s” successfully.\n" filename;
  let rho = check 1 rho gma e VSet in
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
  | ex -> Printf.printf "uncaught exception: %s" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintError ex; default

let checkAndEval rho gma (exp : exp) =
  let t = checkI 1 rho gma exp in
  let v = eval exp rho in
  Printf.printf "TYPE: %s\nEVAL: %s\n" (Expr.showValue t) (Expr.showValue v)

let rho : rho ref   = ref Nil
let gma : gamma ref = ref []
let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let filename = Sys.argv.(i) in let chan = open_in filename in
    let exp = Parser.exp Lexer.main (Lexing.from_channel chan) in
    close_in chan;
    let (rho1, gma1) =
      handleErrors (checkMain filename !rho !gma) exp
                   (!rho, !gma) in
    rho := rho1; gma := gma1
  done;
  while true do
    print_string "> ";
    let line = read_line () in
    let exp = Parser.repl Lexer.main (Lexing.from_string line) in
    handleErrors (checkAndEval !rho !gma) exp ()
  done