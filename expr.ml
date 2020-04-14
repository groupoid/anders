type name = string

type patt =
| Pair of patt * patt
| Unit
| Var of name

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

type value =
| VLam of clos
| VPair of value * value
| VSet
| VPi of value * clos
| VSig of value * clos
| VNt of neut
and neut =
| NGen of int
| NApp of neut * value
| NFst of neut
| NSnd of neut
and clos = patt * exp * rho
and rho =
| Nil
| UpVar of rho * patt * value
| UpDec of rho * decl

type nexp =
| NELam of int * nexp
| NEPair of nexp * nexp
| NESet
| NEPi of nexp * int * nexp
| NESig of nexp * int * nexp
| NENt of nneut
and nneut =
| NtGen of int
| NtApp of nneut * nexp
| NtFst of nneut
| NtSnd of nneut
and nrho =
| Nil
| UpVar of nrho * patt * nexp
| UpDec of nrho * decl