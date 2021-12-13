open Ident

type tag = (string option) ref

(* Language Expressions *)

type exp =
  | EPre of int | EKan of int                                                          (* cosmos *)
  | EVar of name | EHole                                                            (* variables *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp             (* pi *)
  | ESig of exp * (name * exp) | EPair of tag * exp * exp                               (* sigma *)
  | EFst of exp | ESnd of exp | EField of exp * string                                  (* sigma *)
  | EId of exp | ERef of exp | EJ of exp                                      (* strict equality *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                     (* path equality *)
  | EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp       (* CCHM interval *)
  | ETransp of exp * exp | EHComp of exp * exp * exp * exp                     (* Kan operations *)
  | EPartial of exp | EPartialP of exp * exp | ESystem of exp System.t      (* partial functions *)
  | ESub of exp * exp * exp | EInc of exp * exp | EOuc of exp                (* cubical subtypes *)
  | EGlue of exp                                                                      (* glueing *)

type tele = name * exp

type scope = Local | Global

(* Intermediate type checker values *)

type value =
  | VKan of int | VPre of int
  | Var of name * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp of value * value
  | VSig of value * clos | VPair of tag * value * value | VFst of value | VSnd of value
  | VId of value | VRef of value | VJ of value
  | VPathP of value | VPLam of value | VAppFormula of value * value
  | VI | VDir of dir | VAnd of value * value | VOr of value * value | VNeg of value
  | VTransp of value * value | VHComp of value * value * value * value
  | VPartialP of value * value | VSystem of value System.t
  | VSub of value * value * value | VInc of value * value | VOuc of value
  | VGlue of value

and clos = name * (value -> value)

and term = Exp of exp | Value of value

and record = scope * term * term

and ctx = record Env.t

(* Implementation *)

let eLam p a b = ELam (a, (p, b))
let ePi  p a b = EPi  (a, (p, b))
let eSig p a b = ESig (a, (p, b))

let ezero = EDir Zero
let eone  = EDir One
let vzero = VDir Zero
let vone  = VDir One

let isOne i = VApp (VApp (VId VI, VDir One), i)
let extFace x e = e (List.map (fun (p, v) -> Var (p, isOne v)) x)

let name x = Name (x, 0)
let decl x = EVar (name x)

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal (ctx : ctx) (p : name) t v = upVar p (Local, Value t, Value v) ctx
let upGlobal (ctx : ctx) (p : name) t v = upVar p (Global, Value t, Value v) ctx

let isGlobal : record -> bool = function Global, _, _ -> false | Local, _, _ -> true
let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n
let mapFace fn phi = Env.fold (fun p d -> Env.add (fn p) d) phi Env.empty
let freshFace ns = mapFace (freshVar ns)
