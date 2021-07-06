open Ident

type scope = Local | Global

let showDir : dir -> string = function
  | Zero -> !zeroPrim | One -> !onePrim

let showAtom (p, d) = Printf.sprintf "(%s = %s)" (showName p) (showDir d)

let showConjunction xs =
    Conjunction.elements xs
    |> List.map showAtom
    |> String.concat " "

let showSystem xs show =
  List.map (fun (x, e) -> Printf.sprintf "%s -> %s" (showConjunction x) (show e)) xs
  |> String.concat ", " |> fun x -> "[" ^ x ^ "]"

type exp =
  | ELam   of tele * exp
  | EKan   of int
  | EPi    of tele * exp
  | ESig   of tele * exp
  | EPair  of exp * exp
  | EFst   of exp
  | ESnd   of exp
  | EApp   of exp * exp
  | EVar   of name
  | EAxiom of string * exp
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
  | EI | EDir of dir
  | EAnd of exp * exp
  | EOr  of exp * exp
  | ENeg of exp
and tele = name * exp
and system = (conjunction * exp) list

let eLam x y = ELam (x, y)
let ePi  x y = EPi  (x, y)
let eSig x y = ESig (x, y)

let name x = Name (x, 0)
let decl x = EVar (name x)

let getVar x =
  let xs = [(!zeroPrim, EDir Zero);
            (!onePrim, EDir One);
            (!intervalPrim, EI)] in
  match List.assoc_opt x xs with
  | Some e -> e | None -> decl x

let rec telescope (f : tele -> exp -> exp) (e : exp) : tele list -> exp = function
  | []      -> e
  | x :: xs -> f x (telescope f e xs)

let impl a b = EPi ((No, a), b)

let rec pLam e : name list -> exp = function
  | [] -> e
  | x :: xs -> EPLam (ELam ((x, EI), pLam e xs))

let getDigit x = Char.chr (x + 0x80) |> Printf.sprintf "\xE2\x82%c"
let rec showLevel x =
  if x < 0 then failwith "showLevel: expected positive integer"
  else if x = 0 then "" else showLevel (x / 10) ^ getDigit (x mod 10)

let rec showExp : exp -> string = function
  | EKan n -> "U" ^ showLevel n
  | ELam (p, x) -> Printf.sprintf "λ %s, %s" (showTele p) (showExp x)
  | EPi (p, x) -> let (var, dom) = p in begin match var with
    | No -> Printf.sprintf "(%s → %s)" (showExp dom) (showExp x)
    | _  -> Printf.sprintf "Π %s, %s" (showTele p) (showExp x)
  end
  | ESig (p, x) -> Printf.sprintf "Σ %s, %s" (showTele p) (showExp x)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> showExp exp ^ ".1"
  | ESnd exp -> showExp exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "(%s %s)" (showExp f) (showExp x)
  | EVar p -> showName p
  | EHole -> "?"
  | EAxiom (p, _) -> p
  | EPre n -> "V" ^ showLevel n
  | EPathP e -> "PathP " ^ showExp e
  | EId e -> Printf.sprintf "Id %s" (showExp e)
  | ERef e -> Printf.sprintf "ref %s" (showExp e)
  | EJ e -> Printf.sprintf "idJ %s" (showExp e)
  | ETransp (p, i) -> Printf.sprintf "transp %s %s" (showExp p) (showExp i)
  | EPLam (ELam ((i, _), e)) -> Printf.sprintf "(<%s> %s)" (showName i) (showExp e)
  | EPLam _ -> failwith "showExp: unreachable code was reached"
  | EAppFormula (f, x) -> Printf.sprintf "(%s @ %s)" (showExp f) (showExp x)
  | EPartial e -> Printf.sprintf "Partial %s" (showExp e)
  | ESystem x -> showSystem x showExp
  | EI -> !intervalPrim | EDir d -> showDir d
  | EAnd (a, b) -> Printf.sprintf "(%s /\\ %s)" (showExp a) (showExp b)
  | EOr (a, b) -> Printf.sprintf "(%s \\/ %s)" (showExp a) (showExp b)
  | ENeg a -> Printf.sprintf "-%s" (showExp a)
and showTele : tele -> string =
  fun (p, x) -> Printf.sprintf "(%s : %s)" (showName p) (showExp x)

let fresh ns n = match Env.find_opt n ns with
  | Some x -> x
  | None   -> n

let freshConj ns = Conjunction.map (fun (p, d) -> (fresh ns p, d))

let rec salt (ns : name Env.t) : exp -> exp = function
  | ELam ((p, a), b)    -> let x = pat p in ELam ((x, salt ns a), salt (Env.add p x ns) b)
  | EKan n              -> EKan n
  | EPi ((p, a), b)     -> let x = pat p in EPi ((x, salt ns a), salt (Env.add p x ns) b)
  | ESig ((p, a), b)    -> let x = pat p in ESig ((x, salt ns a), salt (Env.add p x ns) b)
  | EPair (a, b)        -> EPair (salt ns a, salt ns b)
  | EFst e              -> EFst (salt ns e)
  | ESnd e              -> ESnd (salt ns e)
  | EApp (f, x)         -> EApp (salt ns f, salt ns x)
  | EVar x              -> EVar (fresh ns x)
  | EAxiom (p, e)       -> EAxiom (p, salt ns e)
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

let freshExp = salt Env.empty

type decl =
  | NotAnnotated of string * exp
  | Annotated of string * exp * exp

let freshDecl : decl -> decl = function
  | Annotated (p, exp1, exp2) -> Annotated (p, freshExp exp1, freshExp exp2)
  | NotAnnotated (p, exp) -> NotAnnotated (p, freshExp exp)

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
  | VLam   of value * clos
  | VKan   of int
  | VPi    of value * clos
  | VSig   of value * clos
  | VPair  of value * value
  | VFst   of value
  | VSnd   of value
  | VApp   of value * value
  | Var    of name * value
  | VAxiom of string * value
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
and term =
  | Exp   of exp
  | Value of value
and record = scope * term * term
and ctx = record Env.t

let isGlobal : record -> bool = function
  | Global, _, _ -> false
  | Local,  _, _ -> true

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
  | VAxiom (p, _) -> p
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
and showRho ctx : string =
  Env.bindings ctx |> List.filter_map showTermBind |> String.concat ", "
and showTele p x rho : string =
  if isRhoVisible rho then
    Printf.sprintf "(%s : %s, %s)" (showName p) (showValue x) (showRho rho)
  else Printf.sprintf "(%s : %s)" (showName p) (showValue x)
and showTerm : term -> string = function
  | Exp e   -> showExp e
  | Value v -> showValue v

let showGamma (ctx : ctx) : string =
  Env.bindings ctx
  |> List.filter_map
      (fun (p, x) -> match x with
        | Local, t, _ -> Some (Printf.sprintf "%s : %s" (showName p) (showTerm t))
        | _, _, _ -> None)
  |> String.concat "\n"

let ezero = EDir Zero
let eone  = EDir One

let vzero = VDir Zero
let vone  = VDir One

type command =
  | Nope
  | Eval    of exp
  | Action  of string
  | Command of string * exp