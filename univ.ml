open Ident
open Error
open Expr

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (ExpectedSig u)

let isSet : value -> bool = function
  | VKan _ -> true
  | VPre _ -> true
  | _      -> false

let extSet : value -> int = function
  | VPre n | VKan n -> n
  | v -> raise (ExpectedVSet v)

let isFibrant : value -> bool = function
  | VKan _ -> true
  | _      -> false

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VPre u, VKan v | VKan u, VPre v -> VPre (max u v)
  | u, v -> ExpectedVSet (if isSet u then v else u) |> raise

let univImpl a b = match a, b with
  | VKan u, VKan v | VPre u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VKan u, VPre v -> VPre (max u v)
  | u, v -> ExpectedVSet (if isSet u then v else u) |> raise

let implv a b ctx = VPi (a, (No, b, ctx))
