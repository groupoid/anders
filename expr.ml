open Ident

(* Interface *)

type exp =
  | ELam   of exp * (name * exp)
  | EKan   of int
  | EPi    of exp * (name * exp)
  | ESig   of exp * (name * exp)
  | EPair  of exp * exp
  | EFst   of exp
  | ESnd   of exp
  | EApp   of exp * exp
  | EVar   of name
  | EHole
  (* cubical part *)
  | EPre        of int
  | EId         of exp
  | ERef        of exp
  | EJ          of exp
  | EPathP      of exp
  | ETransp     of exp * exp
  | EPLam       of exp
  | EAppFormula of exp * exp
  | EPartial    of exp
  | ESystem     of system
  | EI
  | EDir of dir
  | EAnd of exp * exp
  | EOr  of exp * exp
  | ENeg of exp
and system = (conjunction * exp) list

type tele = name * exp

type decl =
  | Def of string * exp option * exp
  | Axiom of string * exp

type line =
  | Import of string
  | Option of string * string
  | Decl of decl

type content = line list
type file = string * content
type scope = Local | Global

type value =
  | VLam   of value * clos
  | VKan   of int
  | VPi    of value * clos
  | VSig   of value * clos
  | VPair  of value * value
  | VFst   of value
  | VSnd   of value
  | VApp   of value * value
  | Var    of name * value
  | VHole
  (* cubical part *)
  | VPre        of int
  | VId         of value
  | VRef        of value
  | VPLam       of value
  | VJ          of value
  | VPathP      of value
  | VTransp     of value * value
  | VAppFormula of value * value
  | VPartial    of value
  | VSystem     of system * ctx
  | VI | VDir of dir
  | VAnd of value * value
  | VOr  of value * value
  | VNeg of value
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

let fresh ns n = match Env.find_opt n ns with Some x -> x | None -> n
let freshConj ns = Conjunction.map (fun (p, d) -> (fresh ns p, d))

let rec telescope (ctor : name -> exp -> exp -> exp) (e : exp) : tele list -> exp = function
  | (p, a) :: xs -> ctor p a (telescope ctor e xs)
  | [] -> e
let rec pLam e : name list -> exp = function [] -> e | x :: xs -> EPLam (ELam (EI, (x, pLam e xs)))

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"
let getVar x =
  let xs = [(!zeroPrim, EDir Zero); (!onePrim, EDir One); (!intervalPrim, EI)] in
  match List.assoc_opt x xs with Some e -> e | None -> decl x

let impl a b = EPi (a, (No, b))
let prod a b = ESig (a, (No, b))

let rec salt (ns : name Env.t) : exp -> exp = function
  | ELam (a, (p, b))    -> saltTele eLam ns p a b
  | EKan n              -> EKan n
  | EPi (a, (p, b))     -> saltTele ePi ns p a b
  | ESig (a, (p, b))    -> saltTele eSig ns p a b
  | EPair (a, b)        -> EPair (salt ns a, salt ns b)
  | EFst e              -> EFst (salt ns e)
  | ESnd e              -> ESnd (salt ns e)
  | EApp (f, x)         -> EApp (salt ns f, salt ns x)
  | EVar x              -> EVar (fresh ns x)
  | EHole               -> EHole
  | EPre n              -> EPre n
  | EId e               -> EId (salt ns e)
  | ERef e              -> ERef (salt ns e)
  | EJ e                -> EJ (salt ns e)
  | EPathP e            -> EPathP (salt ns e)
  | ETransp (p, i)      -> ETransp (salt ns p, salt ns i)
  | EPLam e             -> EPLam (salt ns e)
  | EAppFormula (p, i)  -> EAppFormula (salt ns p, salt ns i)
  | EPartial e          -> EPartial (salt ns e)
  | ESystem x           -> ESystem (List.map (fun (phi, e) -> (freshConj ns phi, salt ns e)) x)
  | EI                  -> EI
  | EDir d              -> EDir d
  | EAnd (a, b)         -> EAnd (salt ns a, salt ns b)
  | EOr (a, b)          -> EOr (salt ns a, salt ns b)
  | ENeg e              -> ENeg (salt ns e)
and saltTele ctor ns p a b =
  let x = pat p in ctor x (salt ns a) (salt (Env.add p x ns) b)

let freshExp = salt Env.empty
let freshDecl : decl -> decl = function
  | Def (p, Some exp1, exp2) -> Def (p, Some (freshExp exp1), freshExp exp2)
  | Def (p, None, exp) -> Def (p, None, freshExp exp)
  | Axiom (p, exp) -> Axiom (p, freshExp exp)

let rec showLevel x =
  if x < 0 then failwith "showLevel: expected positive integer"
  else if x = 0 then "" else showLevel (x / 10) ^ getDigit (x mod 10)

let showDir : dir -> string = function | Zero -> !zeroPrim | One -> !onePrim
let showAtom (p, d) = Printf.sprintf "(%s = %s)" (showName p) (showDir d)
let showConjunction xs = Conjunction.elements xs |> List.map showAtom |> String.concat " "
let showSystem xs show =
  List.map (fun (x, e) -> Printf.sprintf "%s -> %s" (showConjunction x) (show e)) xs
  |> String.concat ", " |> fun x -> "[" ^ x ^ "]"

let rec showExp : exp -> string = function
  | EKan n -> "U" ^ showLevel n
  | ELam (a, (p, b)) -> Printf.sprintf "λ %s, %s" (showTele p a) (showExp b)
  | EPi (a, (p, b)) -> begin match p with
    | No -> Printf.sprintf "(%s → %s)" (showExp a) (showExp b)
    | _  -> Printf.sprintf "Π %s, %s" (showTele p a) (showExp b)
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
  | ESystem x -> showSystem x showExp
  | EI -> !intervalPrim | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "(%s /\\ %s)" (showExp a) (showExp b)
  | EOr (a, b) -> Printf.sprintf "(%s \\/ %s)" (showExp a) (showExp b)
  | ENeg a -> Printf.sprintf "-%s" (showExp a)
and showTele p x = Printf.sprintf "(%s : %s)" (showName p) (showExp x)

let rec showValue : value -> string = function
  | VKan n -> "U" ^ showLevel n
  | VLam (x, (p, e, rho)) -> Printf.sprintf "λ %s, %s" (showTele p x rho) (showExp e)
  | VPi (x, (p, e, rho)) -> begin match p with
    | No -> Printf.sprintf "(%s → %s)" (showValue x) (showExp e)
    | _  -> Printf.sprintf "Π %s, %s" (showTele p x rho) (showExp e)
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
  | VSystem (x, _) -> showSystem x showExp
  | VI -> !intervalPrim | VDir d -> showDir d
  | VAnd (a, b) -> Printf.sprintf "(%s /\\ %s)" (showValue a) (showValue b)
  | VOr (a, b) -> Printf.sprintf "(%s \\/ %s)" (showValue a) (showValue b)
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

type command =
  | Nope
  | Eval    of exp
  | Action  of string
  | Command of string * exp

let showDecl : decl -> string = function
  | Def (p, Some exp1, exp2) -> Printf.sprintf "def %s : %s := %s" p (showExp exp1) (showExp exp2)
  | Def (p, None, exp) -> Printf.sprintf "def %s := %s" p (showExp exp)
  | Axiom (p, exp) -> Printf.sprintf "axiom %s : %s" p (showExp exp)

let showLine : line -> string = function
  | Import p -> Printf.sprintf "import %s" p
  | Option (opt, value) -> Printf.sprintf "option %s %s" opt value
  | Decl d -> showDecl d

let showContent x = String.concat "\n" (List.map showLine x)
let showFile : file -> string = function | (p, x) -> Printf.sprintf "module %s where\n%s" p (showContent x)
