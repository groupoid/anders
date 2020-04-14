type name = string

type patt =
| Unit
| Var of name
| Pair of patt * patt

let rec showPatt : patt -> string = function
  | Unit        -> "_"
  | Var s       -> s
  | Pair (x, y) -> Printf.sprintf "(%s, %s)" (showPatt x) (showPatt y)

type exp =
| ELam of patt * exp
| ESet
| EPi of patt * exp * exp
| ESig of patt * exp * exp
| EPair of exp * exp
| EFst of exp
| ESnd of exp
| EApp of exp * exp
| EVar of name
| EDec of decl * exp
and decl = patt * exp * exp

let rec showExp : exp -> string = function
  | ELam (patt, exp) -> Printf.sprintf "λ %s, %s" (showPatt patt) (showExp exp)
  | ESet -> "U"
  | EPi (patt, exp1, exp2) ->
    Printf.sprintf "Π (%s : %s), %s" (showPatt patt) (showExp exp1) (showExp exp2)
  | ESig (patt, exp1, exp2) ->
    Printf.sprintf "Σ (%s : %s), %s" (showPatt patt) (showExp exp1) (showExp exp2)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> showExp exp ^ ".1"
  | ESnd exp -> showExp exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "(%s %s)" (showExp f) (showExp x)
  | EVar name -> name
  | EDec (decl, exp) -> showDecl decl ^ "\n" ^ showExp exp
and showDecl : decl -> string = function
  (patt, exp1, exp2) -> Printf.sprintf "def %s : %s := %s"
                                       (showPatt patt)
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
| NGen of int * name
| NApp of neut * value
| NFst of neut
| NSnd of neut
and clos = patt * exp * rho
and rho =
| Nil
| UpVar of rho * patt * value
| UpDec of rho * decl

let rec showValue : value -> string = function
  | VLam clos -> let (x, f) = showClos clos in
                 Printf.sprintf "λ %s, %s" x f
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VSet -> "U"
  | VPi (value, clos) ->
    let (x, f) = showClos clos in
    Printf.sprintf "Π (%s : %s), %s" (showValue value) x f
  | VSig (value, clos) ->
    let (x, f) = showClos clos in
    Printf.sprintf "Σ (%s : %s), %s" (showValue value) x f
  | VNt n -> showNeut n
and showNeut : neut -> string = function
  | NGen (k, s) -> s ^ "#" ^ string_of_int k
  | NApp (f, x) -> Printf.sprintf "(%s %s)" (showNeut f) (showValue x)
  | NFst v -> showNeut v ^ ".1"
  | NSnd v -> showNeut v ^ ".2"
and showClos : clos -> string * string = function
  (patt, exp, _) -> (showPatt patt, showExp exp)
