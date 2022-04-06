open Language.Encode
open Language.Spec
open Term
open Rbv

let traceHole v ctx =
  let gma =
    Env.bindings ctx
    |> List.filter_map
        (fun (p, x) -> match x with
          | Local, Value v, _ -> Some (p, rbV v)
          | Local, Exp e, _   -> Some (p, e)
          | _, _, _           -> None) in
  Serialize.resp (Hole (rbV v, gma)); flush_all ()

let trace x xs = Serialize.resp (Trace (x, xs)); flush_all ()

let traceCheck e t  = if !Prefs.trace then trace "CHECK" [e; rbV t]
let traceInfer e    = if !Prefs.trace then trace "INFER" [e]
let traceInferV v   = if !Prefs.trace then trace "INFERV" [rbV v]
let traceEval e     = if !Prefs.trace then trace "EVAL" [e]
let traceClos e p v = if !Prefs.trace then trace "CLOSBYVAL" [e; EVar p; rbV v]
let traceConv v1 v2 = if !Prefs.trace then trace "CONV" [rbV v1; rbV v2]
let traceEqNF v1 v2 = if !Prefs.trace then trace "EQNF" [rbV v1; rbV v2]
