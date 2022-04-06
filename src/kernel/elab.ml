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

let extSup : value -> value * value = function
  | VApp (VApp (VSup _, a), f) -> (a, f)
  | v                          -> raise (Internal (ExpectedSup (rbV v)))

let isInf : value -> bool = function
  | VInf _ -> true | _ -> false

let isSup : value -> bool = function
  | VApp (VApp (VSup _, _), _) -> true | _ -> false

let join = function
  | VInf v -> v
  | v      -> VJoin v

let inf = function
  | VJoin v -> v
  | v       -> VInf v

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
  | EW (a, (p, b))       -> saltTele eW ns p a b
  | ESup (a, b)          -> ESup (salt ns a, salt ns b)
  | EIndW (a, b, c)      -> EIndW (salt ns a, salt ns b, salt ns c)
  | EIm e                -> EIm (salt ns e)
  | EInf e               -> EInf (salt ns e)
  | EIndIm (a, b)        -> EIndIm (salt ns a, salt ns b)
  | EJoin e              -> EJoin (salt ns e)

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
  | W (t, (x, g))        -> W (swap i j t, (x, g >> swap i j))
  | VSup (a, b)          -> VSup (swap i j a, swap i j b)
  | VIndW (a, b, c)      -> VIndW (swap i j a, swap i j b, swap i j c)
  | VIm v                -> VIm (swap i j v)
  | VInf v               -> VInf (swap i j v)
  | VIndIm (a, b)        -> VIndIm (swap i j a, swap i j b)
  | VJoin v              -> VJoin (swap i j v)

and swapVar i j k = if i = k then j else k

let rec mem y = function
  | Var (x, _) -> x = y
  | VLam (t, (x, g)) | VPi (t, (x, g))
  | VSig (t, (x, g)) | W (t, (x, g)) -> memClos y t x g
  | VSystem ts -> System.exists (fun mu v -> Env.mem y mu || mem y v) ts
  | VKan _ | VPre _ | VHole | VI | VEmpty | VUnit
  | VStar | VBool | VFalse | VTrue | VDir _ -> false
  | VPLam a | VFst a | VSnd a | VPathP a | VId a | VRef a
  | VJ a | VNeg a | VOuc a | VGlue a | VIndEmpty a
  | VIndUnit a | VIndBool a | VIm a | VInf a | VJoin a -> mem y a
  | VApp (a, b) | VPartialP (a, b) | VAppFormula (a, b)
  | VTransp (a, b) | VAnd (a, b) | VOr (a, b) | VInc (a, b)
  | VSup (a, b) | VIndIm (a, b) | VPair (_, a, b) -> mem y a || mem y b
  | VSub (a, b, c) | VGlueElem (a, b, c) | VUnglue (a, b, c)
  | VIndW (a, b, c) -> mem y a || mem y b || mem y c
  | VHComp (a, b, c, d) -> mem y a || mem y b || mem y c || mem y d

and memClos y t x g = if x = y then false else mem y (g (Var (x, t)))

let extErr = function
  | Internal err -> err
  | exc          -> Unknown (Printexc.to_string exc)

let extTraceback = function
  | Traceback (err, es) -> (err, es)
  | err                 -> (err, [])
