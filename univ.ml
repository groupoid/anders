open Ident
open Error
open Expr

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

let implv a b ctx = VPi (a, (No, b, ctx))
