open Ident
open Error
open Expr

let rec orNeut : neut * neut -> neut = function
  | NOne, _  | _, NOne  -> NOne
  | NZero, f | f, NZero -> f
  | NOr (f, g), h -> orNeut (f, orNeut (g, h))
  | f, g -> NOr (f, g)

let rec andNeut : neut * neut -> neut = function
  | NZero, _ | _, NZero -> NZero
  | NOne, f  | f, NOne  -> f
  | NAnd (f, g), h -> andNeut (f, andNeut (g, h))
  | NOr (f, g), h | h, NOr (f, g) ->
    orNeut (andNeut (f, h), andNeut (g, h))
  | f, g -> NAnd (f, g)

let rec negNeut : neut -> neut = function
  | NZero       -> NOne
  | NOne        -> NZero
  | NVar p      -> NNeg (NVar p)
  | NNeg n      -> n
  | NAnd (f, g) -> orNeut (negNeut f, negNeut g)
  | NOr (f, g)  -> andNeut (negNeut f, negNeut g)
  | k           -> raise (InvalidFormulaNeg (VNt k))

let andFormula a b =
  match a, b with
  | VNt u, VNt v -> VNt (andNeut (u, v))
  | _, _         -> raise (InvalidFormulaAnd (a, b))

let orFormula a b =
  match a, b with
  | VNt u, VNt v -> VNt (orNeut (u, v))
  | _, _         -> raise (InvalidFormulaOr (a, b))

let negFormula a =
  match a with
  | VNt u -> VNt (negNeut u)
  | _     -> raise (InvalidFormulaNeg a)

module Atom = struct
  type t = name * bool
  let compare (a, x) (b, y) =
    if a = b then Bool.compare x y else Name.compare a b
end

module Atoms = Set.Make(Atom)

let rec extAnd : neut -> Atoms.t = function
  | NVar x               -> Atoms.singleton (x, true)
  | NNeg (NVar x)        -> Atoms.singleton (x, false)
  | NAxiom (x, _)        -> Atoms.singleton (name x, true)
  | NNeg (NAxiom (x, _)) -> Atoms.singleton (name x, false)
  | NAnd (x, y)          -> Atoms.union (extAnd x) (extAnd y)
  | k -> failwith (Printf.sprintf "“%s” expected to be conjuction (should never happen)" (showNeut k))

type disjunction = Atoms.t list
let rec extOr : neut -> disjunction = function
  | NOr (x, y) -> List.rev_append (extOr x) (extOr y)
  | k          -> [extAnd k]

let uniq f =
  let super x y = not (Atoms.equal x y) && Atoms.subset y x in
  List.filter (fun x -> not (List.exists (super x) f)) f

let orSubset xs ys =
  List.for_all (fun y -> List.exists (Atoms.equal y) xs) ys

let orEq f g =
  let f' = uniq (extOr f) in let g' = uniq (extOr g) in
  orSubset f' g' && orSubset g' f'

let andEq f g = Atoms.equal (extAnd f) (extAnd g)