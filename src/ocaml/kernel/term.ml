open Language.Spec

type scope = Local | Global

(* Intermediate type checker values *)

type value =
  | VKan of Z.t | VPre of Z.t
  | Var of ident * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp of value * value
  | VSig of value * clos | VPair of tag * value * value | VFst of value | VSnd of value
  | VId of value | VRef of value | VJ of value
  | VPathP of value | VPLam of value | VAppFormula of value * value
  | VI | VDir of dir | VAnd of value * value | VOr of value * value | VNeg of value
  | VTransp of value * value | VHComp of value * value * value * value
  | VPartialP of value * value | VSystem of value System.t
  | VSub of value * value * value | VInc of value * value | VOuc of value
  | VGlue of value | VGlueElem of value * value * value | VUnglue of value * value * value
  | VEmpty | VIndEmpty of value
  | VUnit | VStar | VIndUnit of value
  | VBool | VFalse | VTrue | VIndBool of value
  | W of value * clos | VSup of value * value | VIndW of value * value * value
  | VNat | VZero | VSucc of value | VIndNat of value * value * value
  | VCoequ of value * value * value * value | VIota2 of value * value * value * value * value
  | VResp of value * value * value * value * value | VIndCoequ of value * value * value * value * value * value * value
  | VDisc of value * value | VBase of value * value * value | VHub of value * value * value | VSpoke of value * value * value * value | VIndDisc of value * value * value * value * value * value
  | VIm of value | VInf of value | VIndIm of value * value | VJoin of value
  | VFla of value | VFlaUnit of value | VFlaCounit of value | VIndFla of value * value
and clos = ident * (value -> value)

type term = Exp of exp | Value of value

and record = scope * term * term

and ctx = record Env.t

(* Implementation *)

let dir d = VDir d
let dim i = Var (i, VI)
let vzero = VDir Zero
let vone  = VDir One

let isOne i = VApp (VApp (VId VI, VDir One), i)
let extFace x e = e (List.map (fun (p, v) -> Var (p, isOne v)) x)

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal ctx p t v = upVar p (Local, Value t, Value v) ctx
let upGlobal ctx p t v = upVar p (Global, Value t, Value v) ctx

let isGlobal : record -> bool = function Global, _, _ -> false | Local, _, _ -> true
let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n
let mapFace fn phi = Env.fold (fun p d -> Env.add (fn p) d) phi Env.empty
let freshFace ns = mapFace (freshVar ns)

exception Internal of error
exception IncompatibleFaces

module IdentSet = Set.Make(Ident)

let rec support = function
  | VKan _ | VPre _ | VHole | VI | VDir _
  | VEmpty | VUnit | VStar | VBool | VFalse | VTrue | VNat | VZero -> IdentSet.empty
  | Var (x, t) -> IdentSet.add x (support t)
  | VPi (t, (x, g)) | VLam (t, (x, g)) | VSig (t, (x, g)) | W (t, (x, g)) ->
    IdentSet.union (support t) (IdentSet.remove x (support (g (Var (x, VI)))))
  | VApp (f, x) | VPair (_, f, x) | VPartialP (f, x) | VAppFormula (f, x)
  | VTransp (f, x) | VAnd (f, x) | VOr (f, x) | VInc (f, x) | VSup (f, x)
  | VIndIm (f, x) | VIndFla (f, x) -> IdentSet.union (support f) (support x)
  | VFst v | VSnd v | VId v | VRef v | VJ v | VPathP v | VPLam v
  | VIndEmpty v | VIndUnit v | VIndBool v | VSucc v | VIm v | VInf v
  | VJoin v | VFla v | VFlaUnit v | VFlaCounit v | VOuc v | VGlue v -> support v
  | VSystem ts -> System.fold (fun mu v acc ->
    let acc = Env.fold (fun x _ s -> IdentSet.add x s) mu acc in
    IdentSet.union acc (support v)) ts IdentSet.empty
  | VHComp (t, r, u, u0) -> IdentSet.union (support t) (IdentSet.union (support r) (IdentSet.union (support u) (support u0)))
  | VSub (a, i, u) | VGlueElem (a, i, u) | VUnglue (a, i, u) | VIndW (a, i, u) ->
    IdentSet.union (support a) (IdentSet.union (support i) (support u))
  | VCoequ (a, b, f, g) -> IdentSet.union (support a) (IdentSet.union (support b) (IdentSet.union (support f) (support g)))
  | VIota2 (a, b, f, g, c) | VResp (a, b, f, g, c) ->
    IdentSet.union (support a) (IdentSet.union (support b) (IdentSet.union (support f) (IdentSet.union (support g) (support c))))
  | VIndCoequ (a, b, f, g, x, i, p) ->
    IdentSet.union (support a) (IdentSet.union (support b) (IdentSet.union (support f) (IdentSet.union (support g) (IdentSet.union (support x) (IdentSet.union (support i) (support p))))))
  | VDisc (s, a) -> IdentSet.union (support s) (support a)
  | VBase (s, a, x) -> IdentSet.union (support s) (IdentSet.union (support a) (support x))
  | VHub (s, a, f) -> IdentSet.union (support s) (IdentSet.union (support a) (support f))
  | VSpoke (s, a, f, x) -> IdentSet.union (support s) (IdentSet.union (support a) (IdentSet.union (support f) (support x)))
  | VIndDisc (s, a, x, nc, nh, ns) ->
    IdentSet.union (support s) (IdentSet.union (support a) (IdentSet.union (support x) (IdentSet.union (support nc) (IdentSet.union (support nh) (support ns)))))
  | VIndNat (c, z, s) -> IdentSet.union (support c) (IdentSet.union (support z) (support s))
  | VNeg v -> support v
let support_cache_size = 256
let support_cache = Array.make support_cache_size (VHole, IdentSet.empty)
let support_cache_idx = ref 0
let get_support v =
  let h = (Hashtbl.hash v) land (support_cache_size - 1) in
  let (v', s) = support_cache.(h) in
  if v == v' then s else
  let s = support v in
  support_cache.(h) <- (v, s);
  s
