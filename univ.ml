open Ident
open Error
open Expr

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (ExpectedSig u)

let extSet : value -> int = function
  | VPre n | VKan n -> n
  | v               -> raise (ExpectedVSet v)

let extKan : value -> int = function
  | VKan n -> n
  | v      -> raise (ExpectedFibrant v)

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VPre u, VKan v | VKan u, VPre v -> VPre (max u v)
  | VKan _, _ | VPre _, _ -> raise (ExpectedVSet b)
  | _, _ -> raise (ExpectedVSet a)

let univImpl a b = match a, b with
  | VKan u, VKan v | VPre u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VKan u, VPre v -> VPre (max u v)
  | VKan _, _      | VPre _, _      -> raise (ExpectedVSet b)
  | _, _ -> raise (ExpectedVSet a)

let implv a b ctx = VPi (a, (No, b, ctx))
