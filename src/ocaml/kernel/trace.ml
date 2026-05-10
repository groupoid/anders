open Language.Spec
open Term
open Rbv

let callback = ref (fun (_ : resp) -> ())

let traceHole v ctx =
  let gma =
    Env.bindings ctx
    |> List.filter_map
        (fun (p, x) -> match x with
          | Local, _, Value v, _ -> Some (p, rbV v)
          | Local, _, Exp e, _   -> Some (p, e)
          | _                    -> None) in
  !callback (Hole (rbV v, gma))

let trace x xs = !callback (Trace (x, xs))

let traceCheck e t  = if !Options.trace then trace "CHECK" [e; rbV t]
let traceInfer e    = if !Options.trace then trace "INFER" [e]
let traceInferV v   = if !Options.trace then trace "INFERV" [rbV v]
let traceEval e     = if !Options.trace then trace "EVAL" [e]
let traceClos e p v = if !Options.trace then trace "CLOSBYVAL" [e; EVar p; rbV v]
let traceConv v1 v2 = if !Options.trace then trace "CONV" [rbV v1; rbV v2]
let traceEqNF v1 v2 = if !Options.trace then trace "EQNF" [rbV v1; rbV v2]

