open Ident
open Error
open Expr

let traceHole v gma =
  print_string ("\nHole:\n\n" ^ Expr.showGamma gma ^ "\n" ^ String.make 80 '-' ^ "\n" ^ Expr.showValue v ^ "\n\n")

let traceCheck (e0 : exp) (t0 : value) : unit =
  if !Prefs.trace then (Printf.printf "CHECK: %s : %s\n" (showExp e0) (showValue t0); flush_all ()) else ()

let traceInfer (e0 : exp) : unit =
  if !Prefs.trace then (Printf.printf "INFER: %s\n" (showExp e0); flush_all ()) else ()

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u          -> raise (ExpectedPi u)

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (ExpectedSig u)

let isVSet : value -> bool = function
  | VKan _ -> true
  | VPre _ -> true
  | _      -> false

let isFibrant : value -> bool = function
  | VKan _ -> true
  | _      -> false

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v -> VPre (max u v)
  | VPre u, VKan v -> VPre (max u v)
  | VKan u, VPre v -> VPre (max u v)
  | u, v -> ExpectedVSet (if isVSet u then v else u) |> raise

let implv a b rho = VPi (a, (No, b, rho))
