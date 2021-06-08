open Ident

type dir = Zero | One
type face = dir Env.t

let showDir : dir -> string = function
  | Zero -> "0"
  | One  -> "1"

let negate : dir -> dir = function
  | Zero -> One
  | One  -> Zero

type formula =
  | Dir of dir
  | Atom of name
  | Neg of name
  | And of formula * formula
  | Or of formula * formula

let rec showFormula : formula -> string = function
  | Dir dir    -> showDir dir
  | Atom i     -> showName i
  | Neg i      -> "−" ^ showName i
  | And (f, g) -> showFormula f ^ " ∧ " ^ showFormula g
  | Or (f, g)  -> showFormula f ^ " ∨ " ^ showFormula g

let andFormula : formula * formula -> formula = function
  | Dir Zero, _ -> Dir Zero
  | _, Dir Zero -> Dir Zero
  | Dir One, f  -> f
  | f, Dir One  -> f
  | f, g        -> And (f, g)

let orFormula : formula * formula -> formula = function
  | Dir One, _  -> Dir One
  | _, Dir One  -> Dir One
  | Dir Zero, f -> f
  | f, Dir Zero -> f
  | f, g        -> Or (f, g)

let rec negFormula : formula -> formula = function
  | Dir dir    -> Dir (negate dir)
  | Atom i     -> Neg i
  | Neg i      -> Atom i
  | And (f, g) -> orFormula (negFormula f, negFormula g)
  | Or (f, g)  -> andFormula (negFormula f, negFormula g)