open Formula
open Error
open Ident
open Expr

let vfst : value -> value = function
  | VPair (u, _) -> u
  | VNt k -> VNt (NFst k)
  | v -> raise (ExpectedSig v)

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | VNt k -> VNt (NSnd k)
  | v -> raise (ExpectedSig v)

let lookup (x : name) (lst : gamma) = match Env.find_opt x lst with
  | Some v -> (match v with | Local u | Global u -> u)
  | None -> raise (VariableNotFound x)

let upDec (rho : rho) : decl -> rho = function
  | NotAnnotated (p, e)
  | Annotated (p, _, e) -> Env.add (Name (p, 0)) (Exp e) rho

let iteHole (p : name) a b = match p with
  | No -> a
  | _  -> b

let upVar (rho : rho) (p : name) (v : value) : rho =
  Env.add p (Value v) rho |> iteHole p rho

let upLocal (gma : gamma) (p : name) (v : value) : gamma =
  Env.add p (Local v) gma |> iteHole p gma

let upGlobal (gma : gamma) (p : name) (v : value) : gamma =
  Env.add p (Global v) gma |> iteHole p gma

let gen : int ref = ref 0
let var x = VNt (NVar x)
let pat : name -> name = (gen := !gen + 1); function | No -> No | Name (p, _) -> Name (p, !gen)
let genV n = var (pat n)
let girard : bool ref = ref false
let ieq u v : bool = !girard || u = v

let traceEval (e : exp) : unit = if !Prefs.trace then
  begin Printf.printf "EVAL: %s\n" (showExp e); flush_all () end else ()

let traceClos (e : exp) (p : name) (v : value) : unit = if !Prefs.trace then
  begin Printf.printf "CLOSBYVAL: (%s)(%s := %s)\n" (showExp e) (showName p) (showValue v); flush_all () end else ()

let traceConv (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  begin Printf.printf "CONV: %s = %s\n" (showValue v1) (showValue v2); flush_all () end else ()

let traceEqNF (v1 : value) (v2 : value) : unit = if !Prefs.trace then
  begin Printf.printf "EQNF: %s = %s\n" (showValue v1) (showValue v2); flush_all () end else ()

let rec eval (e : exp) (rho : rho) = traceEval e; match e with
  | ESet u             -> VSet u
  | ELam ((p, a), b)   -> VLam (eval a rho, (p, b, rho))
  | EPi  ((p, a), b)   -> VPi  (eval a rho, (p, b, rho))
  | ESig ((p, a), b)   -> VSig (eval a rho, (p, b, rho))
  | EFst e             -> vfst (eval e rho)
  | ESnd e             -> vsnd (eval e rho)
  | EApp (f, x)        -> app (eval f rho, eval x rho)
  | EVar x             -> getRho rho x
  | EPair (e1, e2)     -> VPair (eval e1 rho, eval e2 rho)
  | EHole              -> VNt NHole
  | EAxiom (p, e)      -> VNt (NAxiom (p, eval e rho))
and app : value * value -> value = function
  | VLam (_, f), v     -> closByVal f v
  | VNt k, m           -> VNt (NApp (k, m))
  | x, y               -> raise (InvalidApplication (x, y))
and getRho rho x = match Env.find_opt x rho with
  | Some (Value v)     -> v
  | Some (Exp e)       -> eval e rho
  | None               -> raise (VariableNotFound x)
and closByVal (x : clos) (v : value) = let (p, e, rho) = x in
  begin traceClos e p v; eval e (upVar rho p v) end

let rec rbV : value  -> exp = function
  | VLam (t, g)      -> let (p, _, _) = g in let q = pat p in ELam ((q, rbV t), rbV (closByVal g (var q)))
  | VPair (u, v)     -> EPair (rbV u, rbV v)
  | VSet u           -> ESet u
  | VPi (t, g)       -> let (p, _, _) = g in let q = pat p in EPi ((q, rbV t), rbV (closByVal g (var q)))
  | VSig (t, g)      -> let (p, _, _) = g in let q = pat p in ESig ((q, rbV t), rbV (closByVal g (var q)))
  | VNt l            -> rbN l
and rbN : neut -> exp = function
  | NVar s           -> EVar s
  | NApp (k, m)      -> EApp (rbN k, rbV m)
  | NFst k           -> EFst (rbN k)
  | NSnd k           -> ESnd (rbN k)
  | NHole            -> EHole
  | NAxiom (p, v)    -> EAxiom (p, rbV v)

let prune rho x = match Env.find_opt x rho with
  | Some (Value v)   -> rbV v
  | Some (Exp e)     -> e
  | None             -> raise (VariableNotFound x)

let rec weak (e : exp) (rho : rho) = match e with
  | ESet u           -> ESet u
  | ELam ((p, a), b) -> weakTele eLam rho p a b
  | EPi  ((p, a), b) -> weakTele ePi  rho p a b
  | ESig ((p, a), b) -> weakTele eSig rho p a b
  | EFst e           -> EFst (weak e rho)
  | ESnd e           -> ESnd (weak e rho)
  | EApp (f, x)      -> EApp (weak f rho, weak x rho)
  | EVar x           -> prune rho x
  | EPair (e1, e2)   -> EPair (weak e1 rho, weak e2 rho)
  | EHole            -> EHole
  | EAxiom (p, e)    -> EAxiom (p, weak e rho)
and weakTele ctor rho p a b : exp =
  ctor (p, weak a rho) (weak b (upVar rho p (var p)))

let rec conv v1 v2 : bool = traceConv v1 v2; v1 = v2 || match v1, v2 with
  | VSet u, VSet v -> ieq u v
  | VNt x, VNt y -> convNeut x y
  | VPair (a, b), VPair (c, d) -> conv a c && conv b d
  | VPair (a, b), v -> conv a (vfst v) && conv b (vsnd v)
  | v, VPair (a, b) -> conv (vfst v) a && conv (vsnd v) b
  | VPi (a, g), VPi (b, h) | VSig (a, g), VSig (b, h)
  | VLam (a, g), VLam (b, h) -> let (p, e1, rho1) = g in let (q, e2, rho2) = h in
    let v = genV p in conv a b &&
      (weak e1 (upVar rho1 p v) = weak e2 (upVar rho2 q v) ||
       conv (closByVal g v) (closByVal h v))
  | VLam (a, (p, o, v)), b -> let u = genV p in conv (closByVal (p, o, v) u) (app (b, u))
  | b, VLam (a, (p, o, v)) -> let u = genV p in conv (app (b, u)) (closByVal (p, o, v) u)
  | _, _ -> false
and convNeut n1 n2 : bool = match n1, n2 with
  | NVar a, NVar b -> a = b
  | NApp (f, a), NApp (g, b) -> convNeut f g && conv a b
  | NFst x, NFst y -> convNeut x y
  | NSnd x, NSnd y -> convNeut x y
  | NAxiom (p, x), NAxiom (q, y) -> p = q && conv x y
  | _, _ -> false

let eqNf v1 v2 : unit = traceEqNF v1 v2; if conv v1 v2 then () else raise (TypeIneq (v1, v2))
