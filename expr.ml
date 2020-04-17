exception ParsingError

type name =
| Hole
| Name of string * int

let showName : name -> string = function
  | Hole        -> "_"
  | Name (s, _) -> s

type exp =
| ELam of tele * exp
| ESet
| EPi of tele * exp
| ESig of tele * exp
| EPair of exp * exp
| EFst of exp
| ESnd of exp
| EApp of exp * exp
| EVar of name
| EDec of decl * exp
and decl = name * exp * exp
and tele = name * exp

(* In OCaml constructors are not functions. *)
let eLam x y = ELam (x, y)
let ePi x y  = EPi  (x, y)
let eSig x y = ESig (x, y)

let rec cotele (f : tele -> exp -> exp) (e : exp) : tele list -> exp = function
  | []      -> e
  | [x]     -> f x e
  | x :: xs -> f x (cotele f e xs)

let rec showExp : exp -> string = function
  | ESet -> "U"
  | ELam (p, x) -> Printf.sprintf "\\%s -> %s" (showTele p) (showExp x)
  | EPi  (p, x) -> Printf.sprintf "%s -> %s"   (showTele p) (showExp x)
  | ESig (p, x) -> Printf.sprintf "%s * %s"    (showTele p) (showExp x)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> showExp exp ^ ".1"
  | ESnd exp -> showExp exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "(%s %s)" (showExp f) (showExp x)
  | EVar p -> showName p
  | EDec (decl, exp) -> showDecl decl ^ "\n" ^ showExp exp
and showDecl : decl -> string = function
  (p, exp1, exp2) -> Printf.sprintf "def %s : %s := %s"
                                    (showName p)
                                    (showExp exp1)
                                    (showExp exp2)
and showTele : tele -> string = function
  (p, x) -> Printf.sprintf "(%s : %s)" (showName p) (showExp x)

type value =
| VLam of value * clos
| VPair of value * value
| VSet
| VPi of value * clos
| VSig of value * clos
| VNt of neut
and neut =
| NVar of name
| NApp of neut * value
| NFst of neut
| NSnd of neut
and clos = name * exp * rho
and rho =
| Nil
| UpVar of rho * name * value
| UpDec of rho * decl

let rec showValue : value -> string = function
  | VLam (x, (p, e, rho)) ->
    Printf.sprintf "\\%s -> %s" (showTele p x rho) (showExp e)
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VSet -> "U"
  | VPi (x, (p, e, rho)) ->
    Printf.sprintf "%s -> %s" (showTele p x rho) (showExp e)
  | VSig (x, (p, e, rho)) ->
    Printf.sprintf "%s * %s" (showTele p x rho) (showExp e)
  | VNt n -> showNeut n
and showNeut : neut -> string = function
  | NVar s -> showName s
  | NApp (f, x) -> Printf.sprintf "(%s %s)" (showNeut f) (showValue x)
  | NFst v -> showNeut v ^ ".1"
  | NSnd v -> showNeut v ^ ".2"
and showTele p x : rho -> string = function
  | UpDec (rho, _) -> showTele p x rho
  | Nil -> Printf.sprintf "(%s : %s)" (showName p) (showValue x)
  | rho -> Printf.sprintf "(%s : %s, %s)" (showName p) (showValue x) (showRho rho)
and isRhoInvisible : rho -> bool = function
  | Nil     -> true
  | UpDec _ -> true
  | _       -> false
and showRho : rho -> string = function
  | UpVar (u, p, v) when isRhoInvisible u ->
    Printf.sprintf "%s := %s" (showName p) (showValue v)
  | UpVar (rho, p, v) ->
    Printf.sprintf "%s := %s, %s" (showName p) (showValue v) (showRho rho)
  | UpDec (rho, _) -> showRho rho
  | Nil -> ""

type gamma = (name * value) list