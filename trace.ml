open Ident
open Expr

let traceHole v gma =
  print_string ("\nHole:\n\n" ^ Expr.showGamma gma ^ "\n" ^ String.make 80 '-' ^ "\n" ^ Expr.showValue v ^ "\n\n")

let traceCheck (e0 : exp) (t0 : value) : unit =
  if !Prefs.trace then (Printf.printf "CHECK: %s : %s\n" (showExp e0) (showValue t0); flush_all ()) else ()

let traceInfer (e0 : exp) : unit =
  if !Prefs.trace then (Printf.printf "INFER: %s\n" (showExp e0); flush_all ()) else ()

let traceEval (e : exp) : unit = if !Prefs.trace then
  begin Printf.printf "EVAL: %s\n" (showExp e); flush_all () end else ()

let traceWeak (e : exp) : unit = if !Prefs.trace then
  begin Printf.printf "WEAK: %s\n" (showExp e); flush_all () end else ()

let traceRbV (v : value) : unit = if !Prefs.trace then
  begin Printf.printf "RBV: %s\n" (showValue v); flush_all () end else ()

let traceRbN (n : neut) : unit = if !Prefs.trace then
  begin Printf.printf "RBN: %s\n" (showNeut n); flush_all () end else ()

let traceClos (e : exp) (p : name) (v : value) : unit = if !Prefs.trace then
  begin Printf.printf "CLOSBYVAL: (%s)(%s := %s)\n" (showExp e) (showName p) (showValue v); flush_all () end else ()

let traceConv (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  begin Printf.printf "CONV: %s = %s\n" (showValue v1) (showValue v2); flush_all () end else ()

let traceEqNF (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  begin Printf.printf "EQNF: %s = %s\n" (showValue v1) (showValue v2); flush_all () end else ()
