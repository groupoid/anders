open Expr
open Error

let typeInType : bool ref = ref false
let ieq u v : bool = !typeInType || u = v

let vfst : value -> value = function
  | VPair (u, _) -> u
  | VNt k        -> VNt (NFst k)
  | v            -> raise (ExpectedSig v)

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | VNt k        -> VNt (NSnd k)
  | v            -> raise (ExpectedSig v)

let lookup (x : name) (lst : gamma) =
  match Env.find_opt x lst with
  | Some v ->
    (match v with
    | Local u
    | Global u -> u)
  | None -> raise (VariableNotFound x)

let upDec (rho : rho) : decl -> rho = function
  | NotAnnotated (p, e)
  | Annotated (p, _, e) -> Env.add p (Exp e) rho

let upVar (rho : rho) (p : name) (v : value) : rho =
  Env.add p (Value v) rho

let upLocal (gma : gamma) (p : name) (v : value) : gamma =
  Env.add p (Local v) gma

let upGlobal (gma : gamma) (p : name) (v : value) : gamma =
  Env.add p (Global v) gma

let rec eval (e : exp) (rho : rho) =
  if !Prefs.trace then
    (Printf.printf "EVAL: %s\n" (showExp e); flush_all ())
  else ();
  match e with
  | ESet u -> VSet u
  | ELam ((p, a), b) -> VLam (eval a rho, (p, b, rho))
  | EPi  ((p, a), b) -> VPi  (eval a rho, (p, b, rho))
  | ESig ((p, a), b) -> VSig (eval a rho, (p, b, rho))
  | EFst e -> vfst (eval e rho)
  | ESnd e -> vsnd (eval e rho)
  | EApp (f, x) -> app (eval f rho, eval x rho)
  | EVar x -> getRho rho x
  | EPair (e1, e2) -> VPair (eval e1 rho, eval e2 rho)
  | EHole -> VNt NHole
  | EUndef -> VNt NUndef
and app : value * value -> value = function
  | VLam (_, f), v -> closByVal f v
  | VNt k, m       -> VNt (NApp (k, m))
  | x, y           -> raise (InvalidApplication (x, y))
and closByVal (x : clos) (v : value) =
  let (p, e, rho) = x in eval e (upVar rho p v)
and getRho rho x =
  match Env.find_opt x rho with
  | Some (Value v) -> v
  | Some (Exp e) -> eval e rho
  | None -> raise (VariableNotFound x)

let pat (k : int) : name -> name = function
  | No          -> No
  | Name (p, _) -> Name (p, k)
let genV k n : value = VNt (NVar (pat k n))

let rec rbV (k : int) : value -> exp = function
  | VLam (t, g)    ->
    let (p, _, _) = g in
    ELam ((pat k p, rbV k t), rbV (k + 1) (closByVal g (genV k p)))
  | VPair (u, v)   -> EPair (rbV k u, rbV k v)
  | VSet u         -> ESet u
  | VPi (t, g)     ->
    let (p, _, _) = g in
    EPi ((pat k p, rbV k t), rbV (k + 1) (closByVal g (genV k p)))
  | VSig (t, g)    ->
    let (p, _, _) = g in
    ESig ((pat k p, rbV k t), rbV (k + 1) (closByVal g (genV k p)))
  | VNt l          -> rbN k l
and rbN i : neut -> exp = function
  | NVar s      -> EVar s
  | NApp (k, m) -> EApp (rbN i k, rbV i m)
  | NFst k      -> EFst (rbN i k)
  | NSnd k      -> ESnd (rbN i k)
  | NHole       -> EHole
  | NUndef      -> EUndef

let rec conv k v1 v2 : bool =
  match v1, v2 with
  | VSet u, VSet v -> ieq u v
  | VNt x, VNt y -> convNeut k x y
  | VPair (a, b), VPair (c, d) -> conv k a b && conv k b d
  | VLam (a, g), VLam (b, h) ->
    let (p, _, _) = g in let p' = genV k p in
    conv k a b && conv (k + 1) (closByVal g p') (closByVal h p')
  | VLam (a, g), b ->
    let (p, _, _) = g in let p' = genV k p in
    conv (k + 1) (closByVal g p') (app (b, p'))
  | b, VLam (a, g) ->
    let (p, _, _) = g in let p' = genV k p in
    conv (k + 1) (app (b, p')) (closByVal g p')
  | VPi (a, g), VPi (b, h) -> conv k (VLam (a, g)) (VLam (b, h))
  | VSig (a, g), VSig (b, h) -> conv k (VLam (a, g)) (VLam (b, h))
  | _, _ -> false
and convNeut k n1 n2 : bool =
  match n1, n2 with
  | NVar a, NVar b -> a = b
  | NApp (f, a), NApp (g, b) -> convNeut k f g && conv k a b
  | NFst x, NFst y -> convNeut k x y
  | NSnd x, NSnd y -> convNeut k x y
  | _, _ -> false

let eqNf k v1 v2 : unit =
  if conv k v1 v2 then ()
  else raise (TypeIneq (v1, v2))