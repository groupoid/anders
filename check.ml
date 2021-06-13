open Formula
open Error
open Ident
open Expr
open Univ

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
    | _       -> begin match infer env e with
      | VNt (NApp (NApp (NPathP _, u0), u1)) ->
        begin let y = eval x env in match y with
        | VNt NZero -> u0
        | VNt NOne  -> u1
        | _         -> VAppFormula (v, y) end
      | _ -> raise (InvalidApplication (v, eval x env)) end
    end
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

and prune (rho, gma) x = match Env.find_opt x rho with
  | Some (Value v)   -> rbV gma v
  | Some (Exp e)     -> e
  | None             -> raise (VariableNotFound x)

and weak (e : exp) env = match e with
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

and conv env v1 v2 : bool = let (rho, gma) = env in traceConv v1 v2;
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
  | VLam (a, (p, o, v)), b | b, VLam (a, (p, o, v)) ->
    let u = genV p in conv env (app gma (b, u)) (closByVal gma (p, o, v) u)
  | VPre u, VPre v -> ieq u v
  | VPLam f, VPLam g -> conv env f g
  | VPLam f, v | v, VPLam f -> let p = genV (name "i") in
    conv env (eval (EAppFormula (rbV gma v, rbV gma p)) env) (app gma (f, p))
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

and eqNf env v1 v2 : unit = traceEqNF v1 v2;
  if conv env v1 v2 then () else raise (TypeIneq (v1, v2))

and check env (e0 : exp) (t0 : value) = let (rho, gma) = env in
  traceCheck e0 t0; match e0, t0 with
  | ELam ((p, a), e), VPi (t, g) -> eqNf env (eval a env) t;
    let q = pat p in let gen = var q in
    let gma' = upLocal (upLocal gma p t) q t in
    check (upVar rho p gen, gma') e (closByVal gma g gen)
  | EPair (e1, e2), VSig (t, g) -> let _ = check env e1 t in
    check env e2 (closByVal gma g (eval e1 env))
  | EHole, v -> traceHole v gma
  | EAxiom (_, u), v -> eqNf env (eval u env) v
  | EPLam e, VNt (NApp (NApp (NPathP (VPLam g), u0), u1)) ->
    let v0 = app gma (eval e env, VNt NZero) in
    let v1 = app gma (eval e env, VNt NOne) in
    check env (rbV gma v0) (app gma (g, VNt NZero));
    check env (rbV gma v1) (app gma (g, VNt NOne));
    eqNf env v0 u0; eqNf env v1 u1
  | e, VPre u -> begin
    match infer env e with
    | VKan v | VPre v -> if ieq u v then () else raise (TypeIneq (VPre u, VPre v))
    | t -> raise (TypeIneq (VPre u, t)) end
  | e, t -> eqNf env t (infer env e)

and infer env e0 : value = let (rho, gma) = env in traceInfer e0;
  match e0 with
  | EVar x -> lookup x gma
  | EKan u -> VKan (u + 1)
  | EPi ((p, a), b) ->
    let q = pat p in let gen = var q in let t = eval a env in
    let rho' = upLocal (upLocal gma p t) q t in
    let v = infer (upVar rho p gen, rho') b in imax (infer env a) v
  | ESig (x, y) -> infer env (EPi (x, y))
  | EApp (f, x) -> let (t, g) = extPiG (infer env f) in
    ignore (check env x t); closByVal gma g (eval x env)
  | EFst e -> fst (extSigG (infer env e))
  | ESnd e -> let (_, g) = extSigG (infer env e) in closByVal gma g (vfst (eval e env))
  | EAxiom (_, e) -> eval e env
  | EPre u -> VPre (u + 1)
  | EPathP (EPLam e) ->
    let v = eval e env in
    let v0 = app gma (v, VNt NZero) in
    let v1 = app gma (v, VNt NOne) in
    let t0 = infer env (rbV gma v0) in
    let t1 = infer env (rbV gma v1) in
    begin match t0, t1 with
    | VKan u, VKan v ->
      if ieq u v then implv v0 (impl (rbV gma v1) (EKan u)) rho
      else raise (TypeIneq (VKan u, VKan v))
    | _, _ -> ExpectedFibrant (if isVSet t0 then t1 else t0) |> raise end
  | EAppFormula (f, x) ->
    check env x (VNt NI);
    begin match infer env f with
    | VNt (NApp (NApp (NPathP (VPLam g), _), _)) -> app gma (g, eval x env)
    | _ -> raise (ExpectedPath f) end
  | EI -> VPre 0 | EZero -> VNt NI | EOne -> VNt NI
  | ENeg e ->
    if infer env e = VNt NI
    then VNt NI else raise (InferError e0)
  | EOr (e1, e2) | EAnd (e1, e2) ->
    if infer env e1 = VNt NI && infer env e2 = VNt NI
    then VNt NI else raise (InferError e0)
  | e -> raise (InferError e)
