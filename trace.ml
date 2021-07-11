open Ident
open Expr

let traceHole v gma = print_string ("\nHole:\n\n" ^ Expr.showGamma gma ^ "\n" ^ String.make 80 '-' ^ "\n" ^ Expr.showValue v ^ "\n\n")
let trace x = print_string x; flush_all ()

let traceCheck (e : exp) (t : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "CHECK: %s : %s\n" (showExp e) (showValue t))

let traceInfer (e : exp) : unit = if !Prefs.trace then
  trace (Printf.sprintf "INFER: %s\n" (showExp e))

let traceInferV (v : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "INFERV: %s\n" (showValue v))

let traceEval (e : exp) : unit = if !Prefs.trace then
  trace (Printf.sprintf "EVAL: %s\n" (showExp e))

let traceWeak (e : exp) : unit = if !Prefs.trace then
  trace (Printf.sprintf "WEAK: %s\n" (showExp e))

let traceRbV (v : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "RBV: %s\n" (showValue v))

let traceClos (e : exp) (p : name) (v : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "CLOSBYVAL: (%s)(%s := %s)\n" (showExp e) (showName p) (showValue v))

let traceConv (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "CONV: %s = %s\n" (showValue v1) (showValue v2))

let traceEqNF (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  trace (Printf.sprintf "EQNF: %s = %s\n" (showValue v1) (showValue v2))
