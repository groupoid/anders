open Formula
open Ident

type exp =
  | ELam of tele * exp
  | ESet of int
  | EPi of tele * exp
  | ESig of tele * exp
  | EPair of exp * exp
  | EFst of exp
  | ESnd of exp
  | EApp of exp * exp
  | EVar of name
  | EHole | EAxiom of string * exp
  | EPathP of exp * exp * exp
  | EPLam of name * exp
  | EAppFormula of exp * formula
and tele = name * exp

let eLam x y = ELam (x, y)
let ePi  x y = EPi  (x, y)
let eSig x y = ESig (x, y)

let rec telescope (f : tele -> exp -> exp) (e : exp) : tele list -> exp = function
  | []      -> e
  | [x]     -> f x e
  | x :: xs -> f x (telescope f e xs)

let rec pLam (e : exp) : name list -> exp = function
  | []      -> e
  | x :: xs -> EPLam (x, pLam e xs)

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"
let rec showUniverse x =
  if x < 0 then failwith "showUniverse: expected positive integer"
  else if x = 0 then "" else showUniverse (x / 10) ^ getDigit (x mod 10)

let rec showExp : exp -> string = function
  | ESet 0 -> "U"
  | ESet u -> "U" ^ showUniverse u
  | ELam (p, x) -> Printf.sprintf "λ %s, %s" (showTele p) (showExp x)
  | EPi  (p, x) -> let (var, dom) = p in begin match var with | No -> Printf.sprintf "(%s → %s)" (showExp dom) (showExp x)
                                                              | _  -> Printf.sprintf "Π %s, %s" (showTele p) (showExp x) end
  | ESig (p, x) -> Printf.sprintf "Σ %s, %s" (showTele p) (showExp x)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> showExp exp ^ ".1"
  | ESnd exp -> showExp exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "(%s %s)" (showExp f) (showExp x)
  | EVar p -> showName p
  | EHole -> "?"
  | EAxiom (p, _) -> p
  | EPathP (t, a, b) -> Printf.sprintf "PathP %s %s %s" (showExp t) (showExp a) (showExp b)
  | EPLam (i, e) -> Printf.sprintf "(<%s> %s)" (showName i) (showExp e)
  | EAppFormula (e, f) -> Printf.sprintf "%s @ %s" (showExp e) (showFormula f)
and showTele : tele -> string = function
  | (No, x) -> showExp x
  | (p,  x) -> Printf.sprintf "(%s : %s)" (showName p) (showExp x)

type decl =
  | NotAnnotated of string * exp
  | Annotated of string * exp * exp

let showDecl : decl -> string = function
  | Annotated (p, exp1, exp2) -> Printf.sprintf "def %s : %s := %s" p (showExp exp1) (showExp exp2)
  | NotAnnotated (p, exp) -> Printf.sprintf "def %s := %s" p (showExp exp)

type line =
  | Import of string
  | Option of string * string
  | Decl of decl

type content = line list

type file = string * content

let showLine : line -> string = function
  | Import p -> Printf.sprintf "import %s" p
  | Option (opt, value) -> Printf.sprintf "option %s %s" opt value
  | Decl d -> showDecl d

let showContent x = String.concat "\n" (List.map showLine x)

let showFile : file -> string = function
  | (p, x) -> Printf.sprintf "module %s where\n%s" p (showContent x)

type value =
  | VLam of value * clos
  | VPair of value * value
  | VSet of int
  | VPi of value * clos
  | VSig of value * clos
  | VNt of neut
  | VPathP of value * value * value
  | VPLam of name * value
  | VAppFormula of value * formula
and neut =
  | NVar of name
  | NApp of neut * value
  | NFst of neut
  | NSnd of neut
  | NHole | NAxiom of string * value
and clos = name * exp * rho
and term =
  | Exp of exp
  | Value of value
  | Formula of formula
and rho = term Env.t

(* Compatibility with OCaml 4.05
   From: https://github.com/ocaml/ocaml/blob/trunk/stdlib/list.ml *)
let filterMap f =
  let rec aux accu = function
    | [] -> List.rev accu
    | x :: l ->
      match f x with
      | None -> aux accu l
      | Some v -> aux (v :: accu) l
  in aux []

let isTermVisible : term -> bool = function
  | Exp _   -> false
  | Value _ -> true

let rec showValue : value -> string = function
  | VLam (x, (p, e, rho)) -> Printf.sprintf "λ %s, %s" (showTele p x rho) (showExp e)
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VSet 0 -> "U"
  | VSet u -> "U" ^ showUniverse u
  | VPi (x, (p, e, rho)) -> Printf.sprintf "Π %s, %s" (showTele p x rho) (showExp e)
  | VSig (x, (p, e, rho)) -> Printf.sprintf "Σ %s, %s" (showTele p x rho) (showExp e)
  | VPathP (t, a, b) -> Printf.sprintf "PathP %s %s %s" (showValue t) (showValue a) (showValue b)
  | VPLam (i, e) -> Printf.sprintf "(<%s> %s)" (showName i) (showValue e)
  | VAppFormula (e, f) -> Printf.sprintf "%s @ %s" (showValue e) (showFormula f)
  | VNt n -> showNeut n
and showNeut : neut -> string = function
  | NVar p -> showName p
  | NApp (f, x) -> Printf.sprintf "(%s %s)" (showNeut f) (showValue x)
  | NFst v -> showNeut v ^ ".1"
  | NSnd v -> showNeut v ^ ".2"
  | NHole -> "?"
  | NAxiom (p, _) -> p
and showTermBind : name * term -> string option = function
  | p, Value v -> Some (Printf.sprintf "%s := %s" (showName p) (showValue v))
  | _, _       -> None
and showRho (rho : rho) : string =
  Env.bindings rho |> filterMap showTermBind |> String.concat ", "
and showTele p x rho : string =
  if Env.exists (fun _ -> isTermVisible) rho then
    Printf.sprintf "(%s : %s, %s)" (showName p) (showValue x) (showRho rho)
  else match p with
  | No -> showValue x
  | _  -> Printf.sprintf "(%s : %s)" (showName p) (showValue x)

type scope =
  | Local  of value
  | Global of value
type gamma = scope Env.t

let showGamma (gma : gamma) : string =
  Env.bindings gma
  |> filterMap
      (fun x -> let (p, y) = x in
        match y with
        | Local v -> Some (Printf.sprintf "%s : %s" (showName p) (showValue v))
        | _       -> None)
  |> String.concat "\n"

type command =
  | Nope
  | Eval of exp
  | Action of string
  | Command of string * exp