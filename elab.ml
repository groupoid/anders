open Ident
open Error
open Expr

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u -> raise (ExpectedPi u)

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u -> raise (ExpectedSig u)

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

let idv t x y = VApp (VApp (VId t, x), y)
let implv a b = VPi (a, (Irrefutable, fun _ -> b))

let idp v = VPLam (VLam (VI, (Irrefutable, fun _ -> v)))
let pathv v a b = VApp (VApp (VPathP v, a), b)

let impl a b = EPi (a, (Irrefutable, b))
let prod a b = ESig (a, (Irrefutable, b))

let hcompval u = EApp (EApp (u, ezero), ERef eone)

let rec salt (ns : name Env.t) : exp -> exp = function
  | ELam (a, (p, b))     -> saltTele eLam ns p a b
  | EKan n               -> EKan n
  | EPi (a, (p, b))      -> saltTele ePi ns p a b
  | ESig (a, (p, b))     -> saltTele eSig ns p a b
  | EPair (r, a, b)      -> EPair (r, salt ns a, salt ns b)
  | EFst e               -> EFst (salt ns e)
  | ESnd e               -> ESnd (salt ns e)
  | EField (e, p)        -> EField (salt ns e, p)
  | EApp (f, x)          -> EApp (salt ns f, salt ns x)
  | EVar x               -> EVar (freshVar ns x)
  | EHole                -> EHole
  | EPre n               -> EPre n
  | EId e                -> EId (salt ns e)
  | ERef e               -> ERef (salt ns e)
  | EJ e                 -> EJ (salt ns e)
  | EPathP e             -> EPathP (salt ns e)
  | ETransp (p, i)       -> ETransp (salt ns p, salt ns i)
  | EHComp (t, r, u, u0) -> EHComp (salt ns t, salt ns r, salt ns u, salt ns u0)
  | EPLam e              -> EPLam (salt ns e)
  | EAppFormula (p, i)   -> EAppFormula (salt ns p, salt ns i)
  | EPartial e           -> EPartial (salt ns e)
  | EPartialP (t, r)     -> EPartialP (salt ns t, salt ns r)
  | ESub (a, i, u)       -> ESub (salt ns a, salt ns i, salt ns u)
  | ESystem xs           -> ESystem (System.fold (fun k v -> System.add (freshFace ns k) (salt ns v)) xs System.empty)
  | EInc (t, r)          -> EInc (salt ns t, salt ns r)
  | EOuc e               -> EOuc (salt ns e)
  | EI                   -> EI
  | EDir d               -> EDir d
  | EAnd (a, b)          -> EAnd (salt ns a, salt ns b)
  | EOr (a, b)           -> EOr (salt ns a, salt ns b)
  | ENeg e               -> ENeg (salt ns e)
  | EGlue e              -> EGlue (salt ns e)
  | Empty                -> Empty
  | ERecEmpty e          -> ERecEmpty (salt ns e)
  | EUnit                -> EUnit
  | EStar                -> EStar
  | ERecUnit e           -> ERecUnit (salt ns e)
  | EBool                -> EBool
  | EFalse               -> EFalse
  | ETrue                -> ETrue
  | ERecBool e           -> ERecBool (salt ns e)
  | EW (a, (p, b))       -> saltTele eW ns p a b
  | ESup (a, b)          -> ESup (salt ns a, salt ns b)
  | ERecW (a, b, c)      -> ERecW (salt ns a, salt ns b, salt ns c)

and freshFace ns phi =
  Env.fold (fun k v -> Env.add (freshVar ns k) v) phi Env.empty

and saltTele ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty
