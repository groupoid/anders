open Expr
open Error

let vfst : value -> value = function
  | VPair (u, _) -> u
  | VNt k        -> VNt (NFst k)
  | v            -> raise (ExpectedSig v)

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | VNt k        -> VNt (NSnd k)
  | v            -> raise (ExpectedSig v)

let rec lRho : rho -> int = function
  | Nil               -> 0
  | UpVar (rho, _, _) -> lRho rho + 1
  | UpDec (rho, _)    -> lRho rho

let rec lookup (x1 : name) (lst : gamma) =
  match lst with
  | (x2, v) :: xs -> if x1 = x2 then v else lookup x1 xs
  | []            -> raise (VariableNotFound x1)

let rec eval (e : exp) (rho : rho) =
  match e with
  | ESet -> VSet
  | EDec (d, e) -> eval e (UpDec (rho, d))
  | ELam ((p, a), b) -> VLam (eval a rho, (p, b, rho))
  | EPi  ((p, a), b) -> VPi  (eval a rho, (p, b, rho))
  | ESig ((p, a), b) -> VSig (eval a rho, (p, b, rho))
  | EFst e -> vfst (eval e rho)
  | ESnd e -> vsnd (eval e rho)
  | EApp (f, x) -> app (eval f rho, eval x rho)
  | EVar x -> getRho rho x
  | EPair (e1, e2) -> VPair (eval e1 rho, eval e2 rho)
and app : value * value -> value = function
  | VLam (_, f), v -> closByVal f v
  | VNt k, m       -> VNt (NApp (k, m))
  | x, y           -> raise (InvalidApplication (x, y))
and closByVal (x : clos) (v : value) =
  let (p, e, rho) = x in eval e (UpVar (rho, p, v))
and getRho rho0 x =
  match rho0 with
  | Nil -> raise (VariableNotFound x)
  | UpVar (rho, p, v) ->
    if x = p then v else getRho rho x
  | UpDec (rho, (p, _, e)) ->
    if x = p then eval e rho0 else getRho rho x

let pat (k : int) : name -> name = function
  | Hole        -> Hole
  | Name (p, _) -> Name (p, k)
let genV k n : value = VNt (NVar (pat k n))

let rec rbV (k : int) : value -> exp = function
  | VLam (t, g)    ->
    let (p, _, _) = g in
    ELam ((pat k p, rbV k t), rbV (k + 1) (closByVal g (genV k p)))
  | VPair (u, v)   -> EPair (rbV k u, rbV k v)
  | VSet           -> ESet
  | VPi (t, g)     ->
    let (p, _, _) = g in
    EPi ((pat k p, rbV k t), rbV (k + 1) (closByVal g (genV k p)))
  | VSig (t, g)    ->
    let (p, _, _) = g in
    ESig ((pat k p, rbV k t), rbV (k + 1) (closByVal g (genV k p)))
  | VNt l          -> rbN k l
and rbN i : neut -> exp = function
  | NVar s              -> EVar s
  | NApp (k, m)         -> EApp (rbN i k, rbV i m)
  | NFst k              -> EFst (rbN i k)
  | NSnd k              -> ESnd (rbN i k)

let eqNf i m1 m2 : unit =
  let e1 = rbV i m1 in
  let e2 = rbV i m2 in
  if e1 = e2 then ()
  else raise (TypeMismatch (m1, m2))