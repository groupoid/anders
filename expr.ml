exception ParsingError

type name =
| Hole
| Name of string * int

let showName : name -> string = function
  | Hole        -> "_"
  | Name (s, _) -> s

type exp =
| ELam of name * exp
| ESet
| EPi of name * exp * exp
| ESig of name * exp * exp
| EPair of exp * exp
| EFst of exp
| ESnd of exp
| EApp of exp * exp
| EVar of name
| EDec of decl * exp
and decl = name * exp * exp

let rec lam (e : exp) : name list -> exp = function
  | []      -> raise ParsingError
  | [x]     -> ELam (x, e)
  | x :: xs -> ELam (x, lam e xs)

let rec showExp : exp -> string = function
  | ELam (p, exp) -> Printf.sprintf "λ %s, %s" (showName p) (showExp exp)
  | ESet -> "U"
  | EPi (p, exp1, exp2) ->
    Printf.sprintf "(%s : %s) -> %s" (showName p) (showExp exp1) (showExp exp2)
  | ESig (p, exp1, exp2) ->
    Printf.sprintf "(%s : %s) * %s" (showName p) (showExp exp1) (showExp exp2)
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

type value =
| VLam of clos
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
  | VLam clos -> let (x, f) = showClos clos in
                 Printf.sprintf "λ %s, %s" x f
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VSet -> "U"
  | VPi (value, clos) ->
    let (x, f) = showClos clos in
    Printf.sprintf "Π (%s : %s), %s" x (showValue value) f
  | VSig (value, clos) ->
    let (x, f) = showClos clos in
    Printf.sprintf "Σ (%s : %s), %s" x (showValue value) f
  | VNt n -> showNeut n
and showNeut : neut -> string = function
  | NVar s -> showName s
  | NApp (f, x) -> Printf.sprintf "(%s %s)" (showNeut f) (showValue x)
  | NFst v -> showNeut v ^ ".1"
  | NSnd v -> showNeut v ^ ".2"
and showClos : clos -> string * string = function
  (p, exp, _) -> (showName p, showExp exp)

type gamma = (name * value) list