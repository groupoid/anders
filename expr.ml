open Ident

(* Language Expressions *)

type exp =
  | EPre of int | EKan of int                                                   (* cosmos *)
  | EVar of name | EHole                                                     (* variables *)
  | EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp      (* pi *)
  | ESig of exp * (name * exp) | EPair  of exp * exp | EFst of exp | ESnd of exp (* sigma *)
  | EId of exp | ERef of exp | EJ of exp                               (* strict equality *)
  | EPathP of exp | EPLam of exp | EAppFormula of exp * exp              (* CCHM equality *)
  | EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp     (* Interval *)
  | ETransp of exp * exp | EPartial of exp | ESystem of system          (* Kan operations *)
  | ESub of exp * exp * exp | EInc of exp | EOuc of exp               (* Cubical subtypes *)

and system = Const of exp | Split of (face * exp) list

type tele = name * exp

type scope = Local | Global

(* Intermediate type checker values *)

type value =
  | VKan of int | VPre of int
  | Var of name * value | VHole
  | VPi of value * clos | VLam of value * clos | VApp   of value * value
  | VSig of value * clos | VPair  of value * value | VFst of value | VSnd of value
  | VId of value | VRef of value | VJ of value
  | VPathP of value | VPLam of value | VAppFormula of value * value
  | VI | VDir of dir | VAnd of value * value | VOr of value * value | VNeg of value
  | VTransp of value * value | VPartial of value | VSystem of system * ctx
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

let isGlobal : record -> bool = function Global, _, _ -> false | Local, _, _ -> true

let freshVar ns n = match Env.find_opt n ns with Some x -> x | None -> n

let mapFace fn phi = Env.fold (fun p d -> Env.add (fn p) d) phi Env.empty
let freshFace ns = mapFace (freshVar ns)

let rec telescope (ctor : name -> exp -> exp -> exp) (e : exp) : tele list -> exp = function
  | (p, a) :: xs -> ctor p a (telescope ctor e xs)
  | [] -> e
let rec pLam e : name list -> exp = function [] -> e | x :: xs -> EPLam (ELam (EI, (x, pLam e xs)))

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"
let getVar x =
  let xs = [(!zeroPrim, EDir Zero); (!onePrim, EDir One); (!intervalPrim, EI)] in
  match List.assoc_opt x xs with Some e -> e | None -> decl x

let rec showLevel x =
  if x < 0 then failwith "showLevel: expected positive integer"
  else if x = 0 then "" else showLevel (x / 10) ^ getDigit (x mod 10)

let showDir : dir -> string = function | Zero -> !zeroPrim | One -> !onePrim
let showAtom (p, d) = Printf.sprintf "(%s = %s)" (showName p) (showDir d)
let showFace xs = Env.bindings xs |> List.map showAtom |> String.concat " "
let showSystem show = function
  | Split xs -> List.map (fun (x, e) -> Printf.sprintf "%s → %s" (showFace x) (show e)) xs
                |> String.concat ", "
  | Const x -> Printf.sprintf "_ → %s" (show x)

let rec showExp : exp -> string = function
  | EKan n -> "U" ^ showLevel n
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTele p a) (showExp b)
  | EPi (a, (p, b)) -> begin match p with
    | Irrefutable -> Printf.sprintf "(%s → %s)" (showExp a) (showExp b)
    | _           -> Printf.sprintf "Π %s, %s" (showTele p a) (showExp b)
  end
  | ESig (a, (p, b)) -> Printf.sprintf "Σ %s, %s" (showTele p a) (showExp b)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> showExp exp ^ ".1"
  | ESnd exp -> showExp exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "(%s %s)" (showExp f) (showExp x)
  | EVar p -> showName p
  | EHole -> "?"
  | EPre n -> "V" ^ showLevel n
  | EPathP e -> "PathP " ^ showExp e
  | EId e -> Printf.sprintf "Id %s" (showExp e)
  | ERef e -> Printf.sprintf "ref %s" (showExp e)
  | EJ e -> Printf.sprintf "idJ %s" (showExp e)
  | ETransp (p, i) -> Printf.sprintf "transp %s %s" (showExp p) (showExp i)
  | EPLam (ELam (_, (i, e))) -> Printf.sprintf "(<%s> %s)" (showName i) (showExp e)
  | EPLam _ -> failwith "showExp: unreachable code was reached"
  | EAppFormula (f, x) -> Printf.sprintf "(%s @ %s)" (showExp f) (showExp x)
  | EPartial e -> Printf.sprintf "Partial %s" (showExp e)
  | ESystem x -> Printf.sprintf "[%s]" (showSystem showExp x)
  | ESub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (showExp a) (showExp i) (showExp u)
  | EI -> !intervalPrim | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "(%s ∧ %s)" (showExp a) (showExp b)
  | EOr (a, b) -> Printf.sprintf "(%s ∨ %s)" (showExp a) (showExp b)
  | ENeg a -> Printf.sprintf "-%s" (showExp a)
  | EInc e -> Printf.sprintf "(inc %s)" (showExp e)
  | EOuc e -> Printf.sprintf "(ouc %s)" (showExp e)
and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showExp x)

let rec showValue : value -> string = function
  | VKan n -> "U" ^ showLevel n
  | VLam (x, (p, e, rho)) -> Printf.sprintf "λ %s, %s" (showTele p x rho) (showExp e)
  | VPi (x, (p, e, rho)) -> begin match p with
    | Irrefutable -> Printf.sprintf "(%s → %s)" (showValue x) (showExp e)
    | _           -> Printf.sprintf "Π %s, %s" (showTele p x rho) (showExp e)
  end
  | VSig (x, (p, e, rho)) -> Printf.sprintf "Σ %s, %s" (showTele p x rho) (showExp e)
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VFst v -> showValue v ^ ".1"
  | VSnd v -> showValue v ^ ".2"
  | VApp (f, x) -> Printf.sprintf "(%s %s)" (showValue f) (showValue x)
  | Var (p, _) -> showName p
  | VHole -> "?"
  | VPre n -> "V" ^ showLevel n
  | VPathP v -> "PathP " ^ showValue v
  | VId v -> Printf.sprintf "Id %s" (showValue v)
  | VRef v -> Printf.sprintf "ref %s" (showValue v)
  | VJ v -> Printf.sprintf "idJ %s" (showValue v)
  | VTransp (p, i) -> Printf.sprintf "transp %s %s" (showValue p) (showValue i)
  | VPLam (VLam (_, (p, e, rho))) ->
    if isRhoVisible rho then
      Printf.sprintf "(<%s, %s> %s)" (showName p) (showRho rho) (showExp e)
    else Printf.sprintf "(<%s> %s)" (showName p) (showExp e)
  | VPLam _ -> failwith "showExp: unreachable code was reached"
  | VAppFormula (f, x) -> Printf.sprintf "(%s @ %s)" (showValue f) (showValue x)
  | VPartial v -> Printf.sprintf "Partial %s" (showValue v)
  | VSystem (x, rho) ->
    if isRhoVisible rho then
      Printf.sprintf "[%s, %s]" (showSystem showExp x) (showRho rho)
    else Printf.sprintf "[%s]" (showSystem showExp x)
  | VSub (a, i, u) -> Printf.sprintf "%s[%s ↦ %s]" (showValue a) (showValue i) (showValue u)
  | VInc v -> Printf.sprintf "(inc %s)" (showValue v)
  | VOuc v -> Printf.sprintf "(ouc %s)" (showValue v)
  | VI -> !intervalPrim | VDir d -> showDir d
  | VAnd (a, b) -> Printf.sprintf "(%s ∧ %s)" (showValue a) (showValue b)
  | VOr (a, b) -> Printf.sprintf "(%s ∨ %s)" (showValue a) (showValue b)
  | VNeg a -> Printf.sprintf "-%s" (showValue a)
and showTermBind : name * record -> string option = function
  | p, (Local, _, t) -> Some (Printf.sprintf "%s := %s" (showName p) (showTerm t))
  | _, _             -> None
and isRhoVisible = Env.exists (fun _ -> isGlobal)
and showRho ctx : string = Env.bindings ctx |> List.filter_map showTermBind |> String.concat ", "
and showTele p x rho : string =
  if isRhoVisible rho then Printf.sprintf "(%s : %s, %s)" (showName p) (showValue x) (showRho rho)
  else Printf.sprintf "(%s : %s)" (showName p) (showValue x)
and showTerm : term -> string = function Exp e -> showExp e | Value v -> showValue v

let showGamma (ctx : ctx) : string =
  Env.bindings ctx
  |> List.filter_map
      (fun (p, x) -> match x with
        | Local, t, _ -> Some (Printf.sprintf "%s : %s" (showName p) (showTerm t))
        | _, _, _ -> None)
  |> String.concat "\n"
