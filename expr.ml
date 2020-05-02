type name =
| No
| Name of string * int

let showName : name -> string = function
  | No          -> "_"
  | Name (s, _) -> s

module Name = struct
  type t = name
  let compare x y =
    match (x, y) with
    | No, No -> 0
    | No, Name _ -> -1
    | Name _, No -> 1
    | Name (p, a), Name (q, b) ->
      if p = q then compare a b
      else compare p q
end
module Env = Map.Make(Name)

module Files = Set.Make(String)

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
| EHole
and tele = name * exp

(* In OCaml constructors are not functions. *)
let eLam x y = ELam (x, y)
let ePi  x y = EPi  (x, y)
let eSig x y = ESig (x, y)

let rec cotele (f : tele -> exp -> exp) (e : exp) : tele list -> exp = function
  | []      -> e
  | [x]     -> f x e
  | x :: xs -> f x (cotele f e xs)

let rec showExp : exp -> string = function
  | ESet u -> Printf.sprintf "U %d" u
  | ELam (p, x) -> Printf.sprintf "\\%s -> %s" (showTele p) (showExp x)
  | EPi  (p, x) -> Printf.sprintf "%s -> %s"   (showTele p) (showExp x)
  | ESig (p, x) -> Printf.sprintf "%s * %s"    (showTele p) (showExp x)
  | EPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showExp fst) (showExp snd)
  | EFst exp -> showExp exp ^ ".1"
  | ESnd exp -> showExp exp ^ ".2"
  | EApp (f, x) -> Printf.sprintf "(%s %s)" (showExp f) (showExp x)
  | EVar p -> showName p
  | EHole -> "?"
and showTele : tele -> string = function
  (p, x) -> Printf.sprintf "(%s : %s)" (showName p) (showExp x)

type decl =
  | NotAnnotated of name * exp
  | Annotated of name * exp * exp

let showDecl : decl -> string = function
  | Annotated (p, exp1, exp2) ->
    Printf.sprintf "%s : %s := %s" (showName p) (showExp exp1) (showExp exp2)
  | NotAnnotated (p, exp) ->
    Printf.sprintf "%s := %s" (showName p) (showExp exp)

type content =
| Import of string * content
| Decl of decl * content
| End
type file = string * content

let rec showContent : content -> string = function
  | Import (p, rest) ->
    Printf.sprintf "import %s" p ^ "\n" ^ showContent rest
  | Decl (d, rest) ->
    showDecl d ^ "\n" ^ showContent rest
  | End -> ""

let showFile : file -> string = function
  | (p, x) -> Printf.sprintf "module %s where\n%s" p (showContent x)

type value =
| VLam of value * clos
| VPair of value * value
| VSet of int
| VPi of value * clos
| VSig of value * clos
| VNt of neut
and neut =
| NVar of name
| NApp of neut * value
| NFst of neut
| NSnd of neut
| NHole
and clos = name * exp * rho
and term =
| Exp of exp
| Value of value
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
  | VLam (x, (p, e, rho)) ->
    Printf.sprintf "\\%s -> %s" (showTele p x rho) (showExp e)
  | VPair (fst, snd) -> Printf.sprintf "(%s, %s)" (showValue fst) (showValue snd)
  | VSet u -> Printf.sprintf "U %d" u
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
  | NHole -> "?"
and showTermBind : name * term -> string option = function
  | p, Value v -> Some (Printf.sprintf "%s := %s" (showName p) (showValue v))
  | _, _       -> None
and showRho (rho : rho) : string =
  Env.bindings rho
  |> filterMap showTermBind
  |> String.concat ", "
and showTele p x rho : string =
  if Env.exists (fun _ -> isTermVisible) rho then
    Printf.sprintf "(%s : %s, %s)" (showName p) (showValue x) (showRho rho)
  else Printf.sprintf "(%s : %s)" (showName p) (showValue x)

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
        | _       -> None )
  |> String.concat "\n"

type command =
  | Nope
  | Eval of exp
  | Action of string
  | Command of string * exp