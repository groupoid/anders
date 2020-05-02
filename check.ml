open Expr
open Error
open Eval

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u          -> raise (ExpectedPi u)

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (ExpectedSig u)

let isVSet : value -> bool = function
  | VSet _ -> true
  | u      -> false

let imax a b =
  match a, b with
  | VSet u, VSet v -> VSet (max u v)
  | u, v -> ExpectedVSet (if isVSet u then u else v) |> raise

let rec check k (rho : rho) (gma : gamma) (e0 : exp) (t0 : value) : rho * gamma =
  match e0, t0 with
  | ELam ((p, a), e), VPi (t, g) ->
    eqNf k (eval a rho) t;
    let gen = genV k p in
    let gma1 = upLocal gma p t in
    check (k + 1) (upVar rho p gen) gma1 e (closByVal g gen)
  | EPair (e1, e2), VSig (t, g) ->
    let _ = check k rho gma e1 t in
    check k rho gma e2 (closByVal g (eval e1 rho))
  | EHole, v ->
    print_string ("\nHole:\n\n" ^ Expr.showGamma gma ^ "\n" ^
                  String.make 80 '-' ^ "\n" ^ Expr.showValue v ^ "\n\n");
    (rho, gma)
  | e, t -> eqNf k t (infer k rho gma e); (rho, gma)
and infer k rho gma : exp -> value = function
  | EVar x -> lookup x gma
  | ESet u -> VSet (u + 1)
  | EPi ((p, a), b) ->
    let u = infer k rho gma a in
    let v = infer (k + 1) (upVar rho p (genV k p))
                  (upLocal gma p (eval a rho)) b in
    imax u v
  | ESig (x, y) -> infer k rho gma (EPi (x, y))
  | EApp (f, x) ->
    let (t, g) = extPiG (infer k rho gma f) in
    ignore (check k rho gma x t);
    closByVal g (eval x rho)
  | EFst e -> fst (extSigG (infer k rho gma e))
  | ESnd e ->
    let (_, g) = extSigG (infer k rho gma e) in
    closByVal g (vfst (eval e rho))
  | e -> raise (InferError e)
