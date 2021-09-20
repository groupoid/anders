open Prelude
open Ident

type tag = (string option) ref

(* Language Expressions *)

type exp =
  | EPre of int | EKan of int                                                              (* cosmos *)
  | EVar of name | EHole                                                                (* variables *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp                 (* pi *)
  | ESig of exp * (name * exp) | EPair of tag * exp * exp                                   (* sigma *)
  | EFst of exp | ESnd of exp | EField of exp * string                                      (* sigma *)
  | EId of exp | ERef of exp | EJ of exp                                          (* strict equality *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp                         (* path equality *)
  | EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp           (* CCHM interval *)
  | ETransp of exp * exp | EHComp of exp | EPartial of exp | ESystem of exp system (* Kan operations *)
  | ESub of exp * exp * exp | EInc of exp | EOuc of exp                          (* cubical subtypes *)

and 'a system = ((name * 'a) list * exp) list

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
  | VTransp of value * value | VHComp of value | VPartial of value | VSystem of value system * ctx
  | VSub of value * value * value | VInc of value | VOuc of value

and clos = name * exp * ctx

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

let name x = Name (x, 0)
let decl x = EVar (name x)

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal (ctx : ctx) (p : name) t v : ctx = upVar p (Local, Value t, Value v) ctx
let upGlobal (ctx : ctx) (p : name) t v : ctx = upVar p (Global, Value t, Value v) ctx

let isGlobal : record -> bool = function Global, _, _ -> false | Local, _, _ -> true
let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n
let mapFace fn phi = Env.fold (fun p d -> Env.add (fn p) d) phi Env.empty
let freshFace ns = mapFace (freshVar ns)

let rec telescope (ctor : name -> exp -> exp -> exp) (e : exp) : tele list -> exp = function
  | (p, a) :: xs -> ctor p a (telescope ctor e xs)
  | [] -> e

let rec pLam e : name list -> exp = function [] -> e | x :: xs -> EPLam (ELam (EI, (x, pLam e xs)))

let getVar x =
  let xs = [(!zeroPrim, EDir Zero); (!onePrim, EDir One); (!intervalPrim, EI)] in
  match List.assoc_opt x xs with Some e -> e | None -> decl x

let showDir : dir -> string = function | Zero -> !zeroPrim | One -> !onePrim

let showAtom show = function
  | Irrefutable, t -> Printf.sprintf "(%s = 1)" (show t)
  | x,           t -> Printf.sprintf "(%s : %s = 1)" (showName x) (show t)
let showFace show = List.map (showAtom show) >> String.concat " "

let showSystem showVar showTerm xs =
  List.map (fun (x, e) -> Printf.sprintf "%s → %s" (showFace showVar x) (showTerm e)) xs
  |> String.concat ", "

let parens b x = if b then "(" ^ x ^ ")" else x

let rec ppExp paren e = let x = match e with
  | EKan n -> "U" ^ showSubscript n
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EPi (a, (p, b)) -> showPiExp a p b
  | ESig (a, (p, b)) -> Printf.sprintf "Σ %s, %s" (showTeleExp (p, a)) (showExp b)
  | EPair (_, fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> ppExp true exp ^ ".1"
  | ESnd exp -> ppExp true exp ^ ".2"
  | EField (exp, field) -> ppExp true exp ^ "." ^ field
  | EApp (f, x) -> Printf.sprintf "%s %s" (showExp f) (ppExp true x)
  | EVar p -> showName p
  | EHole -> "?"
  | EPre n -> "V" ^ showSubscript n
  | EPLam (ELam (_, (i, e))) -> Printf.sprintf "<%s> %s" (showName i) (showExp e)
  | EPLam _ -> failwith "showExp: unreachable code was reached"
  | EAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppExp true f) (ppExp true x)
  | ESystem x -> Printf.sprintf "[%s]" (showSystem showExp showExp x)
  | ESub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (ppExp true a) (showExp i) (showExp u)
  | EI -> !intervalPrim | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "%s ∧ %s" (ppExp true a) (ppExp true b)
  | EOr (a, b) -> Printf.sprintf "%s ∨ %s" (ppExp true a) (ppExp true b)
  | ENeg a -> Printf.sprintf "-%s" (ppExp paren a)
  | ETransp (p, i) -> Printf.sprintf "transp %s %s" (ppExp true p) (ppExp true i)
  | EPathP e -> "PathP " ^ ppExp true e
  | EId e -> Printf.sprintf "Id %s" (ppExp true e)
  | ERef e -> Printf.sprintf "ref %s" (ppExp true e)
  | EJ e -> Printf.sprintf "idJ %s" (ppExp true e)
  | EHComp e -> Printf.sprintf "hcomp %s" (ppExp true e)
  | EPartial e -> Printf.sprintf "Partial %s" (ppExp true e)
  | EInc e -> Printf.sprintf "inc %s" (ppExp true e)
  | EOuc e -> Printf.sprintf "ouc %s" (ppExp true e)
  in match e with
  | EVar _ | EFst _ | ESnd _ | EI | EPre _ | ESystem _
  | EKan _ | EHole | EDir _ | EPair _ | ENeg _ -> x
  | _ -> parens paren x

and showExp e = ppExp false e
and showTeleExp (p, x) = Printf.sprintf "(%s : %s)" (showName p) (showExp x)

and showPiExp a p b = match p with
  | Irrefutable -> Printf.sprintf "%s → %s" (ppExp true a) (showExp b)
  | _           -> Printf.sprintf "Π %s, %s" (showTeleExp (p, a)) (showExp b)

let rec ppValue paren v = let x = match v with
  | VKan n -> "U" ^ showSubscript n
  | VLam (x, (p, e, rho)) -> Printf.sprintf "λ %s, %s" (showTeleValue p x rho) (showExp e)
  | VPi (x, (p, e, rho)) -> showPi x p e rho
  | VSig (x, (p, e, rho)) -> Printf.sprintf "Σ %s, %s" (showTeleValue p x rho) (showExp e)
  | VPair (_, fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VFst v -> ppValue true v ^ ".1"
  | VSnd v -> ppValue true v ^ ".2"
  | VApp (f, x) -> Printf.sprintf "%s %s" (showValue f) (ppValue true x)
  | Var (p, _) -> showName p
  | VHole -> "?"
  | VPre n -> "V" ^ showSubscript n
  | VTransp (p, i) -> Printf.sprintf "transp %s %s" (ppValue true p) (ppValue true i)
  | VPLam (VLam (_, (p, e, rho))) -> showLam p e rho
  | VPLam _ -> failwith "showExp: unreachable code was reached"
  | VAppFormula (f, x) -> Printf.sprintf "%s @ %s" (ppValue true f) (ppValue true x)
  | VSystem (x, rho) -> showSystemV x rho
  | VSub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (ppValue true a) (showValue i) (showValue u)
  | VI -> !intervalPrim | VDir d -> showDir d
  | VAnd (a, b) -> Printf.sprintf "%s ∧ %s" (ppValue true a) (ppValue true b)
  | VOr (a, b) -> Printf.sprintf "%s ∨ %s" (ppValue true a) (ppValue true b)
  | VNeg a -> Printf.sprintf "-%s" (ppValue paren a)
  | VPathP v -> "PathP " ^ ppValue true v
  | VId v -> Printf.sprintf "Id %s" (ppValue true v)
  | VRef v -> Printf.sprintf "ref %s" (ppValue true v)
  | VJ v -> Printf.sprintf "idJ %s" (ppValue true v)
  | VPartial v -> Printf.sprintf "Partial %s" (ppValue true v)
  | VHComp v -> Printf.sprintf "hcomp %s" (ppValue true v)
  | VInc v -> Printf.sprintf "inc %s" (ppValue true v)
  | VOuc v -> Printf.sprintf "ouc %s" (ppValue true v)
  in match v with
  | Var _ | VFst _ | VSnd _ | VI | VPre _ | VSystem _
  | VKan _ | VHole | VDir _ | VPair _ | VNeg _ -> x
  | _ -> parens paren x

and showValue v = ppValue false v

and showTeleValue p x rho : string =
  if isRhoVisible rho then Printf.sprintf "(%s : %s, %s)" (showName p) (showValue x) (showRho rho)
  else Printf.sprintf "(%s : %s)" (showName p) (showValue x)

and showLam p e rho =
  if isRhoVisible rho then Printf.sprintf "<%s, %s> %s" (showName p) (showRho rho) (showExp e)
  else Printf.sprintf "<%s> %s" (showName p) (showExp e)

and showSystemV x rho =
  if isRhoVisible rho then Printf.sprintf "[%s, %s]" (showSystem showValue showExp x) (showRho rho)
  else Printf.sprintf "[%s]" (showSystem showValue showExp x)

and showTermBind : name * record -> string option = function
  | p, (Local, _, t) -> Some (Printf.sprintf "%s := %s" (showName p) (showTerm t))
  | _, _             -> None

and showPi x p e rho = match p with
  | Irrefutable ->
    if isRhoVisible rho then Printf.sprintf "(%s, %s) → %s" (showValue x) (showRho rho) (showExp e)
    else Printf.sprintf "%s → %s" (ppValue true x) (showExp e)
  | _           -> Printf.sprintf "Π %s, %s" (showTeleValue p x rho) (showExp e)

and isRhoVisible = Env.exists (fun _ -> isGlobal)

and showRho ctx : string = Env.bindings ctx |> List.filter_map showTermBind |> String.concat ", "

and showTerm : term -> string = function Exp e -> showExp e | Value v -> showValue v

let showGamma (ctx : ctx) : string =
  Env.bindings ctx
  |> List.filter_map
      (fun (p, x) -> match x with
        | Local, t, _ -> Some (Printf.sprintf "%s : %s" (showName p) (showTerm t))
        | _, _, _ -> None)
  |> String.concat "\n"
