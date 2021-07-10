open Ident
open Expr

let traceHole v gma = print_string ("\nHole:\n\n" ^ Expr.showGamma gma ^ "\n" ^ String.make 80 '-' ^ "\n" ^ Expr.showValue v ^ "\n\n")
let trace x = if !Ident.trace then begin print_string x; flush_all () end else ()
let traceCheck (e : exp) (t : value) : unit = trace (Printf.sprintf "CHECK: %s : %s\n" (showExp e) (showValue t))
let traceInfer (e : exp) : unit = trace (Printf.sprintf "INFER: %s\n" (showExp e))
let traceInferV (v : value) : unit = trace (Printf.sprintf "INFERV: %s\n" (showValue v))
let traceEval (e : exp) : unit = trace (Printf.sprintf "EVAL: %s\n" (showExp e))
let traceWeak (e : exp) : unit = trace (Printf.sprintf "WEAK: %s\n" (showExp e))
let traceRbV (v : value) : unit = trace (Printf.sprintf "RBV: %s\n" (showValue v))
let traceClos (e : exp) (p : name) (v : value) : unit = trace (Printf.sprintf "CLOSBYVAL: (%s)(%s := %s)\n" (showExp e) (showName p) (showValue v))
let traceConv (v1 : value) (v2 : value) : unit = trace (Printf.sprintf "CONV: %s = %s\n" (showValue v1) (showValue v2))
let traceEqNF (v1 : value) (v2 : value) : unit = trace (Printf.sprintf "EQNF: %s = %s\n" (showValue v1) (showValue v2))
