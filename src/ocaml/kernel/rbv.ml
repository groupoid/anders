open Language.Spec
open Term

(* Readback *)
let rec rbV v = (*traceRbV v;*) match v with
  | VLam (t, g)          -> rbVTele eLam t g
  | VPair (r, u, v)      -> EPair (r, rbV u, rbV v)
  | VKan u               -> EKan u
  | VPi (t, g)           -> rbVTele ePi t g
  | VSig (t, g)          -> rbVTele eSig t g
  | VPre u               -> EPre u
  | VPLam f              -> EPLam (rbV f)
  | Var (x, _)           -> EVar x
  | VApp (f, x)          -> EApp (rbV f, rbV x)
  | VFst k               -> EFst (rbV k)
  | VSnd k               -> ESnd (rbV k)
  | VHole                -> EHole
  | VPathP v             -> EPathP (rbV v)
  | VPartialP (t, r)     -> EPartialP (rbV t, rbV r)
  | VSystem ts           -> ESystem (System.map rbV ts)
  | VSub (a, i, u)       -> ESub (rbV a, rbV i, rbV u)
  | VTransp (p, i)       -> ETransp (rbV p, rbV i)
  | VHComp (t, r, u, u0) -> EHComp (rbV t, rbV r, rbV u, rbV u0)
  | VAppFormula (f, x)   -> EAppFormula (rbV f, rbV x)
  | VId v                -> EId (rbV v)
  | VRef v               -> ERef (rbV v)
  | VJ v                 -> EJ (rbV v)
  | VI                   -> EI
  | VDir d               -> EDir d
  | VAnd (u, v)          -> EAnd (rbV u, rbV v)
  | VOr (u, v)           -> EOr (rbV u, rbV v)
  | VNeg u               -> ENeg (rbV u)
  | VInc (t, r)          -> EInc (rbV t, rbV r)
  | VOuc v               -> EOuc (rbV v)
  | VGlue v              -> EGlue (rbV v)
  | VGlueElem (r, u, a)  -> EGlueElem (rbV r, rbV u, rbV a)
  | VUnglue (r, u, b)    -> EUnglue (rbV r, rbV u, rbV b)
  | VEmpty               -> EEmpty
  | VIndEmpty v          -> EIndEmpty (rbV v)
  | VUnit                -> EUnit
  | VStar                -> EStar
  | VIndUnit v           -> EIndUnit (rbV v)
  | VBool                -> EBool
  | VFalse               -> EFalse
  | VTrue                -> ETrue
  | VIndBool v           -> EIndBool (rbV v)
  | W (t, g)             -> rbVTele eW t g
  | VSup (a, b)          -> ESup (rbV a, rbV b)
  | VCoequ (a, b, f, g)  -> ECoequ (rbV a, rbV b, rbV f, rbV g)
  | VIota2 (a, b, f, g, c) -> EIota2 (rbV a, rbV b, rbV f, rbV g, rbV c)
  | VResp (a, b, f, g, c) -> EResp (rbV a, rbV b, rbV f, rbV g, rbV c)
  | VIndCoequ (a, b, f, g, x, i, rho) -> EIndCoequ (rbV a, rbV b, rbV f, rbV g, rbV x, rbV i, rbV rho)
  | VDisc (s, a) -> EDisc (rbV s, rbV a)
  | VBase (s, a, x) -> EBase (rbV s, rbV a, rbV x)
  | VHub (s, a, f) -> EHub (rbV s, rbV a, rbV f)
  | VSpoke (s, a, f, x) -> ESpoke (rbV s, rbV a, rbV f, rbV x)
  | VIndDisc (s, a, x, nc, nh, ns', z) -> EIndDisc (rbV s, rbV a, rbV x, rbV nc, rbV nh, rbV ns', rbV z)

  | VIndW (a, b, c)      -> EIndW (rbV a, rbV b, rbV c)
  | VIm t                -> EIm (rbV t)
  | VInf v               -> EInf (rbV v)
  | VJoin v              -> EJoin (rbV v)
  | VIndIm (a, b)        -> EIndIm (rbV a, rbV b)

and rbVTele ctor t (p, g) = let x = Var (p, t) in ctor p (rbV t) (rbV (g x))