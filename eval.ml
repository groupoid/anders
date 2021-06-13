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

let rec eval (e : exp) (env : env) =
  let (rho, gma) = env in traceEval e; match e with
  | EKan u             -> VKan u
  | ELam ((p, a), b)   -> VLam (eval a env, (p, b, rho))
  | EPi  ((p, a), b)   -> VPi  (eval a env, (p, b, rho))
  | ESig ((p, a), b)   -> VSig (eval a env, (p, b, rho))
  | EFst e             -> vfst (eval e env)
  | ESnd e             -> vsnd (eval e env)
  | EApp (f, x)        -> app gma (eval f env, eval x env)
  | EVar x             -> getRho env x
  | EPair (e1, e2)     -> VPair (eval e1 env, eval e2 env)
  | EHole              -> VNt NHole
  | EAxiom (p, e)      -> VNt (NAxiom (p, eval e env))
  | EPre u             -> VPre u
  | EPathP e           -> VNt (NPathP (eval e env))
  | EPLam e            -> VPLam (eval e env)
  | EAppFormula (e, x) ->
    begin let v = eval e env in match v with
    | VPLam f -> app gma (f, eval x env)
    | VNt k   -> VAppFormula (v, eval x env)
    | _       -> raise (InvalidApplication (v, eval x env)) end
  | EI                 -> VNt NI
  | EZero              -> VNt NZero
  | EOne               -> VNt NOne
  | EAnd (e1, e2)      -> andFormula (eval e1 env) (eval e2 env)
  | EOr (e1, e2)       -> orFormula (eval e1 env) (eval e2 env)
  | ENeg e             -> negFormula (eval e env)
and app gma : value * value -> value = function
  | VLam (_, f), v     -> closByVal gma f v
  | VNt k, m           -> VNt (NApp (k, m))
  | x, y               -> raise (InvalidApplication (x, y))
and getRho (rho, gma) x = match Env.find_opt x rho with
  | Some (Value v)     -> v
  | Some (Exp e)       -> eval e (rho, gma)
  | None               -> VNt (NVar x)
and closByVal gma (x : clos) (v : value) = let (p, e, rho) = x in
  begin traceClos e p v; eval e (upVar rho p v, gma) end
and rbV gma : value -> exp = function
  | VLam (t, g)        -> let (p, _, _) = g in let q = pat p in ELam ((q, rbV gma t), rbV gma (closByVal gma g (var q)))
  | VPair (u, v)       -> EPair (rbV gma u, rbV gma v)
  | VKan u             -> EKan u
  | VPi (t, g)         -> let (p, _, _) = g in let q = pat p in EPi ((q, rbV gma t), rbV gma (closByVal gma g (var q)))
  | VSig (t, g)        -> let (p, _, _) = g in let q = pat p in ESig ((q, rbV gma t), rbV gma (closByVal gma g (var q)))
  | VNt l              -> rbN gma l
  | VPre u             -> EPre u
  | VPLam f            -> EPLam (rbV gma f)
  | VAppFormula (f, x) -> EAppFormula (rbV gma f, rbV gma x)
and rbN gma : neut -> exp = function
  | NVar s             -> EVar s
  | NApp (k, m)        -> EApp (rbN gma k, rbV gma m)
  | NFst k             -> EFst (rbN gma k)
  | NSnd k             -> ESnd (rbN gma k)
  | NHole              -> EHole
  | NAxiom (p, v)      -> EAxiom (p, rbV gma v)
  | NPathP v           -> EPathP (rbV gma v)
  | NI                 -> EI
  | NZero              -> EZero
  | NOne               -> EOne
  | NAnd (u, v)        -> EAnd (rbN gma u, rbN gma v)
  | NOr (u, v)         -> EOr (rbN gma u, rbN gma v)
  | NNeg u             -> ENeg (rbN gma u)

let prune (rho, gma) x = match Env.find_opt x rho with
  | Some (Value v)   -> rbV gma v
  | Some (Exp e)     -> e
  | None             -> raise (VariableNotFound x)

let rec weak (e : exp) env = match e with
  | EKan u             -> EKan u
  | ELam ((p, a), b)   -> weakTele eLam env p a b
  | EPi  ((p, a), b)   -> weakTele ePi  env p a b
  | ESig ((p, a), b)   -> weakTele eSig env p a b
  | EFst e             -> EFst (weak e env)
  | ESnd e             -> ESnd (weak e env)
  | EApp (f, x)        -> EApp (weak f env, weak x env)
  | EVar x             -> prune env x
  | EPair (e1, e2)     -> EPair (weak e1 env, weak e2 env)
  | EHole              -> EHole
  | EAxiom (p, e)      -> EAxiom (p, weak e env)
  | EPre u             -> EPre u
  | EPathP u           -> EPathP (weak u env)
  | EPLam u            -> EPLam (weak u env)
  | EAppFormula (f, x) -> EAppFormula (weak f env, weak x env)
  | EI                 -> EI
  | EZero              -> EZero
  | EOne               -> EOne
  | EAnd (e1, e2)      -> EAnd (weak e1 env, weak e2 env)
  | EOr (e1, e2)       -> EOr (weak e1 env, weak e2 env)
  | ENeg e             -> ENeg (weak e env)
and weakTele ctor (rho, gma) p a b : exp =
  ctor (p, weak a (rho, gma)) (weak b (upVar rho p (var p), gma))

let rec conv env v1 v2 : bool = let (rho, gma) = env in traceConv v1 v2;
  v1 = v2 || match v1, v2 with
  | VKan u, VKan v -> ieq u v
  | VNt x, VNt y -> convNeut env x y
  | VPair (a, b), VPair (c, d) -> conv env a c && conv env b d
  | VPair (a, b), v -> conv env a (vfst v) && conv env b (vsnd v)
  | v, VPair (a, b) -> conv env (vfst v) a && conv env (vsnd v) b
  | VPi (a, g), VPi (b, h) | VSig (a, g), VSig (b, h)
  | VLam (a, g), VLam (b, h) -> let (p, e1, rho1) = g in let (q, e2, rho2) = h in
    let v = genV p in conv env a b &&
      (weak e1 (upVar rho1 p v, gma) = weak e2 (upVar rho2 q v, gma) ||
       conv env (closByVal gma g v) (closByVal gma h v))
  | VLam (a, (p, o, v)), b -> let u = genV p in conv env (closByVal gma (p, o, v) u) (app gma (b, u))
  | b, VLam (a, (p, o, v)) -> let u = genV p in conv env (app gma (b, u)) (closByVal gma (p, o, v) u)
  | VPre u, VPre v -> ieq u v
  | VPLam f, VPLam g -> conv env f g
  | VAppFormula (f, x), VAppFormula (g, y) -> conv env f g && conv env x y
  | _, _ -> false
and convNeut env n1 n2 : bool = match n1, n2 with
  | NVar a, NVar b -> a = b
  | NApp (f, a), NApp (g, b) -> convNeut env f g && conv env a b
  | NFst x, NFst y -> convNeut env x y
  | NSnd x, NSnd y -> convNeut env x y
  | NAxiom (p, x), NAxiom (q, y) -> p = q && conv env x y
  | NPathP a, NPathP b -> conv env a b
  | NI, NI -> true
  | NZero, NZero -> true
  | NOne, NOne -> true
  | NOr (x1, y1), NOr (x2, y2) | NAnd (x1, y1), NAnd (x2, y2) ->
    convNeut env x1 x2 && convNeut env y1 y2
  | NNeg x, NNeg y -> convNeut env x y
  | _, _ -> false

let eqNf env v1 v2 : unit = traceEqNF v1 v2;
  if conv env v1 v2 then () else raise (TypeIneq (v1, v2))
