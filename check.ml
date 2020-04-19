open Expr
open Error
open Eval

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u          -> raise (ExpectedPi u)

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (ExpectedSig u)

let rec checkT k rho gma : exp -> rho * gamma = function
  | EPi ((p, a), b) ->
    let _ = checkT k rho gma a in
    let gma1 = Env.add p (eval a rho) gma in
    checkT (k + 1) (upVar rho p (genV k p)) gma1 b
  | ESig ((p, a), b) -> checkT k rho gma (EPi ((p, a), b))
  | ESet -> (rho, gma)
  | u    -> eqNf k VSet (checkI k rho gma u); (rho, gma)
and check k (rho : rho) (gma : gamma) (e0 : exp) (t0 : value) : rho * gamma =
  match e0, t0 with
  | ELam ((p, a), e), VPi (t, g) ->
    eqNf k (eval a rho) t;
    let gen = genV k p in
    let gma1 = Env.add p t gma in
    check (k + 1) (upVar rho p gen) gma1 e (closByVal g gen)
  | EPair (e1, e2), VSig (t, g) ->
    let _ = check k rho gma e1 t in
    check k rho gma e2 (closByVal g (eval e1 rho))
  | EDec (d, e), t ->
    let (name, _, _) = d in
    Printf.printf "Checking: %s\n" (Expr.showName name);
    check k (upDec rho d) (snd (checkD k rho gma d)) e t
  | e, VSet -> checkT k rho gma e
  | e, t -> eqNf k t (checkI k rho gma e); (rho, gma)
and checkI k rho gma : exp -> value = function
  | EVar x -> lookup x gma
  | EApp (f, x) ->
    let t1 = checkI k rho gma f in
    let (t, g) = extPiG t1 in
    ignore (check k rho gma x t);
    closByVal g (eval x rho)
  | EFst e -> fst (extSigG (checkI k rho gma e))
  | ESnd e ->
    let (_, g) = extSigG (checkI k rho gma e) in
    closByVal g (vfst (eval e rho))
  | e -> raise (InferError e)
and checkD k rho gma : decl -> rho * gamma = function
  | (p, a, e) ->
    let _ = checkT k rho gma a in
    let t = eval a rho in let gen = genV k p in
    let gma1 = Env.add p t gma in
    check (k + 1) (upVar rho p gen) gma1 e t