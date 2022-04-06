open Language.Prelude
open Language.Spec

let gidx : int64 ref = ref 0L
let gen () = gidx := Int64.succ !gidx; !gidx

let fresh : ident -> ident = function
  | Irrefutable  -> let n = gen () in Ident ("x" ^ showSubscript (Z.of_int64 n), n)
  | Ident (p, _) -> Ident (p, gen ())

let matchIdent p : ident -> bool = function
  | Irrefutable -> false | Ident (q, _) -> p = q

let freshName x = let n = gen () in Ident (x ^ showSubscript (Z.of_int64 n), n)