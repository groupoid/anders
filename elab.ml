open Prelude
open Ident
open Error
open Expr

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u -> raise (ExpectedPi u)

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u -> raise (ExpectedSig u)

let extSet : value -> Z.t = function
  | VPre n | VKan n -> n
  | v               -> raise (ExpectedVSet v)

let extKan : value -> Z.t = function
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
  | EEmpty               -> EEmpty
  | EIndEmpty e          -> EIndEmpty (salt ns e)
  | EUnit                -> EUnit
  | EStar                -> EStar
  | EIndUnit e           -> EIndUnit (salt ns e)
  | EBool                -> EBool
  | EFalse               -> EFalse
  | ETrue                -> ETrue
  | EIndBool e           -> EIndBool (salt ns e)
  | EW (a, (p, b))       -> saltTele eW ns p a b
  | ESup (a, b)          -> ESup (salt ns a, salt ns b)
  | EIndW (a, b, c)      -> EIndW (salt ns a, salt ns b, salt ns c)

and saltTele ctor ns p a b =
  let x = fresh p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty

(* https://github.com/mortberg/cubicaltt/blob/hcomptrans/Eval.hs#L129
   >This increases efficiency as it won’t trigger computation. *)
let rec swap i j = function
  | VLam (t, (x, g))     -> VLam (swap i j t, (x, g >> swap i j))
  | VPair (r, u, v)      -> VPair (r, swap i j u, swap i j v)
  | VKan u               -> VKan u
  | VPi (t, (x, g))      -> VPi (swap i j t, (x, g >> swap i j))
  | VSig (t, (x, g))     -> VSig (swap i j t, (x, g >> swap i j))
  | VPre u               -> VPre u
  | VPLam f              -> VPLam (swap i j f)
  | Var (k, VI)          -> Var (swapVar i j k, VI)
  | Var (x, t)           -> Var (x, swap i j t)
  | VApp (f, x)          -> VApp (swap i j f, swap i j x)
  | VFst k               -> VFst (swap i j k)
  | VSnd k               -> VSnd (swap i j k)
  | VHole                -> VHole
  | VPathP v             -> VPathP (swap i j v)
  | VPartialP (t, r)     -> VPartialP (swap i j t, swap i j r)
  | VSystem ts           -> VSystem (System.fold (fun k v -> System.add (mapFace (swapVar i j) k) (swap i j v)) ts System.empty)
  | VSub (t, r, u)       -> VSub (swap i j t, swap i j r, swap i j u)
  | VTransp (p, r)       -> VTransp (swap i j p, swap i j r)
  | VHComp (t, r, u, u0) -> VHComp (swap i j t, swap i j r, swap i j u, swap i j u0)
  | VAppFormula (f, x)   -> VAppFormula (swap i j f, swap i j x)
  | VId v                -> VId (swap i j v)
  | VRef v               -> VRef (swap i j v)
  | VJ v                 -> VJ (swap i j v)
  | VI                   -> VI
  | VDir d               -> VDir d
  | VAnd (u, v)          -> VAnd (swap i j u, swap i j v)
  | VOr (u, v)           -> VOr (swap i j u, swap i j v)
  | VNeg u               -> VNeg (swap i j u)
  | VInc (t, r)          -> VInc (swap i j t, swap i j r)
  | VOuc v               -> VOuc (swap i j v)
  | VGlue v              -> VGlue (swap i j v)
  | VEmpty               -> VEmpty
  | VIndEmpty v          -> VIndEmpty (swap i j v)
  | VUnit                -> VUnit
  | VStar                -> VStar
  | VIndUnit v           -> VIndUnit (swap i j v)
  | VBool                -> VBool
  | VFalse               -> VFalse
  | VTrue                -> VTrue
  | VIndBool v           -> VIndBool (swap i j v)
  | W (t, (x, g))        -> W (swap i j t, (x, g >> swap i j))
  | VSup (a, b)          -> VSup (swap i j a, swap i j b)
  | VIndW (a, b, c)      -> VIndW (swap i j a, swap i j b, swap i j c)

and swapVar i j k = if i = k then j else k
