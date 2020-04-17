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

let rec lam (e : exp) : tele list -> exp = function
  | []      -> raise ParsingError
  | [x]     -> ELam (x, e)
  | x :: xs -> ELam (x, lam e xs)

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
  | VLam (value, clos) ->
    let (x, f) = showClos clos in
    Printf.sprintf "\\(%s : %s) -> %s" x (showValue value) f
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VSet -> "U"
  | VPi (value, clos) ->
    let (x, f) = showClos clos in
    Printf.sprintf "(%s : %s) -> %s" x (showValue value) f
  | VSig (value, clos) ->
    let (x, f) = showClos clos in
    Printf.sprintf "(%s : %s) * %s" x (showValue value) f
  | VNt n -> showNeut n
and showNeut : neut -> string = function
  | NVar s -> showName s
  | NApp (f, x) -> Printf.sprintf "(%s %s)" (showNeut f) (showValue x)
  | NFst v -> showNeut v ^ ".1"
  | NSnd v -> showNeut v ^ ".2"
and showClos : clos -> string * string = function
  (p, exp, _) -> (showName p, showExp exp)

type gamma = (name * value) list