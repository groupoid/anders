open Expr

type dir  = Zero | One
type face = dir Env.t

type formula =
  | Dir of dir
  | Atom of name
  | Neg of name
  | And of formula * formula
  | Or of formula * formula