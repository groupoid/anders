open Error
open Expr

let andNeut : neut * neut -> neut = function
  | NZero, _ -> NZero
  | _, NZero -> NZero
  | NOne, f  -> f
  | f, NOne  -> f
  | f, g     -> NAnd (f, g)

let orNeut : neut * neut -> neut = function
  | NOne, _  -> NOne
  | _, NOne  -> NOne
  | NZero, f -> f
  | f, NZero -> f
  | f, g     -> NOr (f, g)

let rec negNeut : neut -> neut = function
  | NZero       -> NOne
  | NOne        -> NZero
  | NVar p      -> NNeg (NVar p)
  | NNeg n      -> n
  | NAnd (f, g) -> andNeut (negNeut f, negNeut g)
  | NOr (f, g)  -> orNeut (negNeut f, negNeut g)
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