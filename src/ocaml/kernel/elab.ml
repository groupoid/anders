open Language.Prelude
open Language.Spec
open Term
open Gen
open Rbv

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u -> raise (Internal (ExpectedPi (rbV u)))

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u -> raise (Internal (ExpectedSig (rbV u)))

let extSet : value -> Z.t = function
  | VPre n | VKan n -> n
  | v               -> raise (Internal (ExpectedType (rbV v)))

let extKan : value -> Z.t = function
  | VKan n -> n
  | v      -> raise (Internal (ExpectedKan (rbV v)))

let extIm : value -> value = function
  | VIm v -> v
  | v     -> raise (Internal (ExpectedIm (rbV v)))

let extInf : value -> value = function
  | VInf v -> v
  | v      -> raise (Internal (ExpectedInf (rbV v)))

let extSucc : value -> value = function
  | VSucc v -> v
  | v       -> raise (Internal (InferError (rbV v)))

let extIota2 : value -> value = function
  | VIota2 (_, _, _, _, v) -> v
  | v                      -> raise (Internal (InferError (rbV v)))

let extBase : value -> value = function
  | VBase (_, _, v) -> v
  | v               -> raise (Internal (InferError (rbV v)))

let extHub : value -> value = function
  | VHub (_, _, f) -> f
  | v              -> raise (Internal (InferError (rbV v)))

let extResp : value -> value = function
  | VResp (_, _, _, _, c) -> c
  | v -> raise (Internal (InferError (rbV v)))

let extSpoke : value -> value * value = function
  | VSpoke (_, _, f, x) -> (f, x)
  | v -> raise (Internal (InferError (rbV v)))

let extSup : value -> value * value = function
  | VApp (VApp (VSup _, a), f) -> (a, f)
  | v                          -> raise (Internal (ExpectedSup (rbV v)))

let isInf : value -> bool = function
  | VInf _ -> true | _ -> false

let isZero : value -> bool = function
  | VZero -> true | _ -> false

let isSucc : value -> bool = function
  | VSucc _ -> true | _ -> false

let isIota2 : value -> bool = function
  | VIota2 _ -> true | _ -> false

let isResp : value -> bool = function
  | VResp _ -> true | _ -> false

let isBase : value -> bool = function
  | VBase _ -> true | _ -> false

let isHub : value -> bool = function
  | VHub _ -> true | _ -> false

let isSpoke : value -> bool = function
  | VSpoke _ -> true | _ -> false

let isSup : value -> bool = function
  | VApp (VApp (VSup _, _), _) -> true | _ -> false

let isRespFormula v = match v with VAppFormula (VResp _, _) -> true | _ -> false
let isSpokeFormula v = match v with VAppFormula (VSpoke _, _) -> true | _ -> false

let extRespFormula v = match v with VAppFormula (VResp (_, _, _, _, c), _) -> c | _ -> raise (Internal (InferError (rbV v)))
let extSpokeFormula v = match v with VAppFormula (VSpoke (_, _, f, x), _) -> (f, x) | _ -> raise (Internal (InferError (rbV v)))

let join = function
  | VInf v -> v
  | v      -> VJoin v

let inf = function
  | VJoin v -> v
  | v       -> VInf v

let flaunit = function
  | VFlaCounit v -> v
  | v            -> VFlaUnit v

let flacounit = function
  | VFlaUnit v -> v
  | v          -> VFlaCounit v

let extFla : value -> value = function
  | VFla v -> v
  | v      -> raise (Internal (ExpectedFla (rbV v)))

let extFlaUnit : value -> value = function
  | VFlaUnit v -> v
  | v          -> raise (Internal (ExpectedFlaUnit (rbV v)))

let extFlaCounit : value -> value = function
  | VFlaCounit v -> v
  | v            -> raise (Internal (ExpectedFlaCounit (rbV v)))

let isFlaUnit : value -> bool = function
  | VFlaUnit _ -> true | _ -> false

let isFlaCounit : value -> bool = function
  | VFlaCounit _ -> true | _ -> false

let inc t r = function
  | VOuc v -> v
  | v      -> VApp (VInc (t, r), v)

let extPathP = function
  | VApp (VApp (VPathP v, u0), u1) -> (v, u0, u1)
  | v                              -> raise (Internal (ExpectedPath (rbV v)))

let extGlue = function
  | VApp (VApp (VGlue t, r), u) -> (t, r, u)
  | v -> raise (Internal (ExpectedGlue (rbV v)))

let extVar ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value (Var (y, _))) -> y
  | Some (_, _, Exp (EVar y)) -> y
  | _ -> x

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v | VPre u, VKan v | VKan u, VPre v -> VPre (max u v)
  | VKan _, _ | VPre _, _ -> raise (Internal (ExpectedType (rbV b)))
  | _, _ -> raise (Internal (ExpectedType (rbV a)))

let impred a b = match a, b with
  | VKan _, VKan v -> VKan v
  | VPre _, VKan v | VKan _, VPre v | VPre _, VPre v -> VPre v
  | VKan _, _ | VPre _, _ -> raise (Internal (ExpectedType (rbV b)))
  | _, _ -> raise (Internal (ExpectedType (rbV a)))

let idv t x y = VApp (VApp (VId t, x), y)
let implv a b = VPi (a, (Irrefutable, fun _ -> b))
let prodv a b = VSig (a, (Irrefutable, fun _ -> b))
let pairv a b = VPair (ref None, a, b)

let idp v = VPLam (VLam (VI, (Irrefutable, fun _ -> v)))
let idfun t = VLam (t, (freshName "x", fun x -> x))
let pathv v a b = VApp (VApp (VPathP v, a), b)

let hcompval u = EApp (EApp (u, ezero), ERef eone)

let ieq u v : bool = !Prefs.girard || u = v
let freshDim () = let i = freshName "ι" in (i, EVar i, Var (i, VI))

let vfst : value -> value = function
  | VPair (_, u, _) -> u
  | v               -> VFst v

let vsnd : value -> value = function
  | VPair (_, _, u) -> u
  | v               -> VSnd v

let eta v = (vfst v, vsnd v)

let rec extByTag p : value -> value option = function
  | VPair (t, fst, snd) ->
  begin match !t with
    | Some q -> if p = q then Some fst else extByTag p snd
    | _      -> extByTag p snd
  end
  | _ -> None

let rec getField p v = function
  | VSig (t, (q, g)) ->
    if matchIdent p q then (vfst v, t)
    else getField p (vsnd v) (g (vfst v))
  | t -> raise (Internal (ExpectedSig (rbV t)))

let rec salt (ns : ident Env.t) : exp -> exp = function
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
  | EGlueElem (r, u, a)  -> EGlueElem (salt ns r, salt ns u, salt ns a)
  | EUnglue (r, u, e)    -> EUnglue (salt ns r, salt ns u, salt ns e)
  | EEmpty               -> EEmpty
  | EIndEmpty e          -> EIndEmpty (salt ns e)
  | EUnit                -> EUnit
  | EStar                -> EStar
  | EIndUnit e           -> EIndUnit (salt ns e)
  | EBool                -> EBool
  | EFalse               -> EFalse
  | ETrue                -> ETrue
  | EIndBool e           -> EIndBool (salt ns e)
  | ENat                 -> ENat
  | EZero                -> EZero
  | ESucc e              -> ESucc (salt ns e)
  | EIndNat (c, z, s)    -> EIndNat (salt ns c, salt ns z, salt ns s)
  | EW (a, (p, b))       -> saltTele eW ns p a b
  | ESup (a, b)          -> ESup (salt ns a, salt ns b)
  | EIndW (a, b, c)      -> EIndW (salt ns a, salt ns b, salt ns c)
  | EIm e                -> EIm (salt ns e)
  | EInf e               -> EInf (salt ns e)
  | EIndIm (a, b)        -> EIndIm (salt ns a, salt ns b)
  | ECoequ (a, b, f, g)  -> ECoequ (salt ns a, salt ns b, salt ns f, salt ns g)
  | EIota2 (a, b, f, g, c) -> EIota2 (salt ns a, salt ns b, salt ns f, salt ns g, salt ns c)
  | EResp (a, b, f, g, c) -> EResp (salt ns a, salt ns b, salt ns f, salt ns g, salt ns c)
  | EIndCoequ (a, b, f, g, x, i, rho) -> EIndCoequ (salt ns a, salt ns b, salt ns f, salt ns g, salt ns x, salt ns i, salt ns rho)
  | EDisc (s, a) -> EDisc (salt ns s, salt ns a)
  | EBase (s, a, x) -> EBase (salt ns s, salt ns a, salt ns x)
  | EHub (s, a, f) -> EHub (salt ns s, salt ns a, salt ns f)
  | ESpoke (s, a, f, x) -> ESpoke (salt ns s, salt ns a, salt ns f, salt ns x)
  | EIndDisc (s, a, x, nc, nh, ns') -> EIndDisc (salt ns s, salt ns a, salt ns x, salt ns nc, salt ns nh, salt ns ns')
  | EJoin e              -> EJoin (salt ns e)
  | EFla e               -> EFla (salt ns e)
  | EFlaUnit e           -> EFlaUnit (salt ns e)
  | EFlaCounit e         -> EFlaCounit (salt ns e)
  | EIndFla (a, b)       -> EIndFla (salt ns a, salt ns b)


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
  | VGlueElem (r, u, a)  -> VGlueElem (swap i j r, swap i j u, swap i j a)
  | VUnglue (r, u, v)    -> VUnglue (swap i j r, swap i j u, swap i j v)
  | VEmpty               -> VEmpty
  | VIndEmpty v          -> VIndEmpty (swap i j v)
  | VUnit                -> VUnit
  | VStar                -> VStar
  | VIndUnit v           -> VIndUnit (swap i j v)
  | VBool                -> VBool
  | VFalse               -> VFalse
  | VTrue                -> VTrue
  | VIndBool v           -> VIndBool (swap i j v)
  | VNat                 -> VNat
  | VZero                -> VZero
  | VSucc v              -> VSucc (swap i j v)
  | VIndNat (c, z, s)    -> VIndNat (swap i j c, swap i j z, swap i j s)
  | W (t, (x, g))        -> W (swap i j t, (x, g >> swap i j))
  | VSup (a, b)          -> VSup (swap i j a, swap i j b)
  | VIndW (a, b, c)      -> VIndW (swap i j a, swap i j b, swap i j c)
  | VIm v                -> VIm (swap i j v)
  | VInf v               -> VInf (swap i j v)
  | VIndIm (a, b)        -> VIndIm (swap i j a, swap i j b)
  | VFla v               -> VFla (swap i j v)
  | VFlaUnit v           -> VFlaUnit (swap i j v)
  | VFlaCounit v         -> VFlaCounit (swap i j v)
  | VIndFla (a, b)       -> VIndFla (swap i j a, swap i j b)
  | VCoequ (a, b, f, g)  -> VCoequ (swap i j a, swap i j b, swap i j f, swap i j g)
  | VIota2 (a, b, f, g, c) -> VIota2 (swap i j a, swap i j b, swap i j f, swap i j g, swap i j c)
  | VResp (a, b, f, g, c) -> VResp (swap i j a, swap i j b, swap i j f, swap i j g, swap i j c)
  | VIndCoequ (a, b, f, g, x, k, rho) -> VIndCoequ (swap i j a, swap i j b, swap i j f, swap i j g, swap i j x, swap i j k, swap i j rho)
  | VDisc (s, a) -> VDisc (swap i j s, swap i j a)
  | VBase (s, a, x) -> VBase (swap i j s, swap i j a, swap i j x)
  | VHub (s, a, f) -> VHub (swap i j s, swap i j a, swap i j f)
  | VSpoke (s, a, f, x) -> VSpoke (swap i j s, swap i j a, swap i j f, swap i j x)
  | VIndDisc (s, a, x, nc, nh, ns') -> VIndDisc (swap i j s, swap i j a, swap i j x, swap i j nc, swap i j nh, swap i j ns')
  | VJoin v              -> VJoin (swap i j v)


and swapVar i j k = if i = k then j else k

let mem y v = IdentSet.mem y (get_support v)

let extErr = function
  | Internal err -> err
  | exc          -> Unknown (Printexc.to_string exc)

let extTraceback = function
  | Traceback (err, es) -> (err, es)
  | err                 -> (err, [])
