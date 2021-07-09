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

let extPathP = function
  | VApp (VApp (VPathP v, u0), u1) -> (v, u0, u1)
  | v                              -> raise (ExpectedPath v)

let extVar ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value (Var (y, _))) -> y
  | Some (_, _, Exp (EVar y)) -> y
  | _ -> x

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

let implv a b ctx = VPi (a, (Irrefutable, b, ctx))

let impl a b = EPi (a, (Irrefutable, b))
let prod a b = ESig (a, (Irrefutable, b))

let rec salt (ns : name Env.t) : exp -> exp = function
  | ELam (a, (p, b))    -> saltTele eLam ns p a b
  | EKan n              -> EKan n
  | EPi (a, (p, b))     -> saltTele ePi ns p a b
  | ESig (a, (p, b))    -> saltTele eSig ns p a b
  | EPair (a, b)        -> EPair (salt ns a, salt ns b)
  | EFst e              -> EFst (salt ns e)
  | ESnd e              -> ESnd (salt ns e)
  | EApp (f, x)         -> EApp (salt ns f, salt ns x)
  | EVar x              -> EVar (freshVar ns x)
  | EHole               -> EHole
  | EPre n              -> EPre n
  | EId e               -> EId (salt ns e)
  | ERef e              -> ERef (salt ns e)
  | EJ e                -> EJ (salt ns e)
  | EPathP e            -> EPathP (salt ns e)
  | ETransp (p, i)      -> ETransp (salt ns p, salt ns i)
  | EPLam e             -> EPLam (salt ns e)
  | EAppFormula (p, i)  -> EAppFormula (salt ns p, salt ns i)
  | EPartial e          -> EPartial (salt ns e)
  | ESub (a, i, u)      -> ESub (salt ns a, salt ns i, salt ns u)
  | ESystem (Split xs)  -> ESystem (Split (List.map (fun (phi, e) -> (freshFace ns phi, salt ns e)) xs))
  | ESystem (Const x)   -> ESystem (Const (salt ns x))
  | EI                  -> EI
  | EDir d              -> EDir d
  | EAnd (a, b)         -> EAnd (salt ns a, salt ns b)
  | EOr (a, b)          -> EOr (salt ns a, salt ns b)
  | ENeg e              -> ENeg (salt ns e)
and saltTele ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty
