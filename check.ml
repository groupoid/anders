open Formula
open Error
open Trace
open Ident
open Prefs
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

let lookup (x : name) (ctx : ctx) =
  match Env.find_opt x ctx with
  | Some (_, v, _) -> v
  | None           -> raise (VariableNotFound x)

let ignoreAnon (p : name) a b = match p with
  | No -> a
  | _  -> b

let upLocal (ctx : ctx) (p : name) t v : ctx =
  Env.add p (Local, t, Value v) ctx |> ignoreAnon p ctx

let upGlobal (ctx : ctx) (p : name) t v : ctx =
  Env.add p (Global, t, Value v) ctx |> ignoreAnon p ctx

let ieq u v : bool = !girard || u = v

let rec eval (e : exp) (ctx : ctx) = traceEval e; match e with
  | EKan u             -> VKan u
  | ELam ((p, a), b)   -> VLam (eval a ctx, (p, b, ctx))
  | EPi  ((p, a), b)   -> VPi  (eval a ctx, (p, b, ctx))
  | ESig ((p, a), b)   -> VSig (eval a ctx, (p, b, ctx))
  | EFst e             -> vfst (eval e ctx)
  | ESnd e             -> vsnd (eval e ctx)
  | EApp (f, x)        -> app ctx (eval f ctx, eval x ctx)
  | EVar x             -> getRho ctx x
  | EPair (e1, e2)     -> VPair (eval e1 ctx, eval e2 ctx)
  | EHole              -> VNt NHole
  | EAxiom (p, e)      -> VNt (NAxiom (p, eval e ctx))
  | EPre u             -> VPre u
  | EPathP e           -> VNt (NPathP (eval e ctx))
  | EPLam e            -> VPLam (eval e ctx)
  | EAppFormula (e, x) ->
    begin match eval e ctx with
    | VPLam f -> app ctx (f, eval x ctx)
    | v       ->
      let (_, u0, u1) = extPathP ctx (rbV ctx v) in
      begin match eval x ctx with
      | VNt (NDir Zero) -> u0
      | VNt (NDir One)  -> u1
      | u               -> VAppFormula (v, u)
      end
    end
  | EIsOne             -> VNt NIsOne
  | EOneRefl           -> VNt NOneRefl
  | EI                 -> VNt NI
  | EDir d             -> VNt (NDir d)
  | EAnd (e1, e2)      -> andFormula (eval e1 ctx) (eval e2 ctx)
  | EOr (e1, e2)       -> orFormula (eval e1 ctx) (eval e2 ctx)
  | ENeg e             -> negFormula (eval e ctx)

and app ctx : value * value -> value = function
  | VLam (t, f), v     -> closByVal ctx t f v
  | VNt k, m           -> VNt (NApp (k, m))
  | x, y               -> raise (InvalidApplication (x, y))

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and closByVal ctx1 t x v = let (p, e, ctx2) = x in traceClos e p v;
  let ctx' = merge ctx2 ctx1 in eval e (upLocal ctx' p t v)

and extPathP ctx e =
  match infer ctx e with
  | VNt (NApp (NApp (NPathP VPLam p, u0), u1)) -> (p, u0, u1)
  | _ -> raise (ExpectedPath e)

and rbV ctx v : exp = traceRbV v; match v with
  | VLam (t, g)        -> rbVTele eLam ctx t g
  | VPair (u, v)       -> EPair (rbV ctx u, rbV ctx v)
  | VKan u             -> EKan u
  | VPi (t, g)         -> rbVTele ePi ctx t g
  | VSig (t, g)        -> rbVTele eSig ctx t g
  | VNt l              -> rbN ctx l
  | VPre u             -> EPre u
  | VPLam f            -> EPLam (rbV ctx f)
  | VAppFormula (f, x) -> EAppFormula (rbV ctx f, rbV ctx x)
and rbN ctx n : exp = traceRbN n; match n with
  | NVar s             -> EVar s
  | NApp (k, m)        -> EApp (rbN ctx k, rbV ctx m)
  | NFst k             -> EFst (rbN ctx k)
  | NSnd k             -> ESnd (rbN ctx k)
  | NHole              -> EHole
  | NAxiom (p, v)      -> EAxiom (p, rbV ctx v)
  | NPathP v           -> EPathP (rbV ctx v)
  | NTransp (p, i)     -> ETransp (rbV ctx p, rbN ctx i)
  | NIsOne             -> EIsOne
  | NOneRefl           -> EOneRefl
  | NI                 -> EI
  | NDir d             -> EDir d
  | NAnd (u, v)        -> EAnd (rbN ctx u, rbN ctx v)
  | NOr (u, v)         -> EOr (rbN ctx u, rbN ctx v)
  | NNeg u             -> ENeg (rbN ctx u)
and rbVTele ctor ctx t g =
  let (p, _, _) = g in let u = pat p in let gen = var u in
  let ctx' = upLocal ctx u t gen in
  ctor (u, rbV ctx t) (rbV ctx' (closByVal ctx' t g gen))

and prune ctx x =
  match Env.find_opt x ctx with
  | Some (_, _, Exp e)   -> e
  | Some (_, _, Value v) -> rbV ctx v
  | None                 -> raise (VariableNotFound x)

and weak (e : exp) ctx = traceWeak e; match e with
  | EVar x             -> prune ctx x
  | ELam ((p, a), b)   -> weakTele eLam ctx p a b
  | EPi  ((p, a), b)   -> weakTele ePi  ctx p a b
  | ESig ((p, a), b)   -> weakTele eSig ctx p a b
  | EFst e             -> EFst (weak e ctx)
  | ESnd e             -> ESnd (weak e ctx)
  | EApp (f, x)        -> EApp (weak f ctx, weak x ctx)
  | EPair (e1, e2)     -> EPair (weak e1 ctx, weak e2 ctx)
  | EAxiom (p, e)      -> EAxiom (p, weak e ctx)
  | EPathP u           -> EPathP (weak u ctx)
  | EPLam u            -> EPLam (weak u ctx)
  | EAppFormula (f, x) -> EAppFormula (weak f ctx, weak x ctx)
  | EAnd (e1, e2)      -> EAnd (weak e1 ctx, weak e2 ctx)
  | EOr (e1, e2)       -> EOr (weak e1 ctx, weak e2 ctx)
  | ENeg e             -> ENeg (weak e ctx)
  | e                  -> e
and weakTele ctor ctx p a b : exp =
  let t = weak a ctx in ctor (p, t) (weak b (upLocal ctx p (eval t ctx) (var p)))

and conv ctx v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || match v1, v2 with
  | VKan u, VKan v -> ieq u v
  | VNt x, VNt y -> convNeut ctx x y
  | VPair (a, b), VPair (c, d) -> conv ctx a c && conv ctx b d
  | VPair (a, b), v | v, VPair (a, b) -> conv ctx (vfst v) a && conv ctx (vsnd v) b
  | VPi (a, g), VPi (b, h) | VSig (a, g), VSig (b, h)
  | VLam (a, g), VLam (b, h) -> let (p, e1, ctx1) = g in let (q, e2, ctx2) = h in
    let u = pat p in let v = var u in let ctx' = upLocal ctx u a v in
    conv ctx a b &&
      (weak e1 (upLocal (merge ctx' ctx1) p a v) =
       weak e2 (upLocal (merge ctx' ctx2) q a v) ||
       conv ctx' (closByVal ctx' a g v) (closByVal ctx' a h v))
  | VLam (a, (p, o, v)), b | b, VLam (a, (p, o, v)) ->
    let u = pat p in let gen = var u in let ctx' = upLocal ctx u a gen in
    conv ctx' (app ctx' (b, gen)) (closByVal ctx' a (p, o, v) gen)
  | VPre u, VPre v -> ieq u v
  | VPLam f, VPLam g -> conv ctx f g
  | VPLam f, v | v, VPLam f -> let p = pat (name "i") in
    let i = var p in let ctx' = upLocal ctx p (VNt NI) i in
    conv ctx' (eval (EAppFormula (rbV ctx' v, EVar p)) ctx') (app ctx' (f, i))
  | VAppFormula (f, x), VAppFormula (g, y) -> conv ctx f g && conv ctx x y
  | _, _ ->
    begin match infer ctx (rbV ctx v1), infer ctx (rbV ctx v2) with
    | VNt (NApp (NIsOne, u1)), VNt (NApp (NIsOne, u2)) -> conv ctx u1 u2
    | _, _ -> false end

and convNeut ctx n1 n2 : bool =
  n1 == n2 || match n1, n2 with
  | NVar u, NVar v -> u = v
  | NApp (f, a), NApp (g, b) -> convNeut ctx f g && conv ctx a b
  | NFst x, NFst y -> convNeut ctx x y
  | NSnd x, NSnd y -> convNeut ctx x y
  | NAxiom (p, x), NAxiom (q, y) -> p = q && conv ctx x y
  | NPathP a, NPathP b -> conv ctx a b
  | NOr _, NOr _ -> orEq n1 n2
  | NAnd _, NAnd _ -> andEq n1 n2
  | NNeg x, NNeg y -> convNeut ctx x y
  | NI, NI -> true
  | NDir u, NDir v -> u = v
  | NIsOne, NIsOne -> true
  | _, _ -> false

and eqNf ctx v1 v2 : unit = traceEqNF v1 v2;
  if conv ctx v1 v2 then () else raise (TypeIneq (v1, v2))

and check ctx (e0 : exp) (t0 : value) =
  traceCheck e0 t0; match e0, t0 with
  | ELam ((p, a), e), VPi (t, g) -> eqNf ctx (eval a ctx) t;
    let u = pat p in let gen = var u in
    let ctx' = upLocal (upLocal ctx p t gen) u t gen in
    check ctx' e (closByVal ctx' t g gen)
  | EPair (e1, e2), VSig (t, g) -> check ctx e1 t;
    check ctx e2 (closByVal ctx t g (eval e1 ctx))
  | EHole, v -> traceHole v ctx
  | EAxiom (_, u), v -> eqNf ctx (eval u ctx) v
  | EPLam e, VNt (NApp (NApp (NPathP (VPLam g), u0), u1)) ->
    let v0 = app ctx (eval e ctx, zero) in
    let v1 = app ctx (eval e ctx, one) in
    check ctx (rbV ctx v0) (app ctx (g, zero));
    check ctx (rbV ctx v1) (app ctx (g, one));
    eqNf ctx v0 u0; eqNf ctx v1 u1
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (TypeIneq (VPre u, VPre v))
    | t -> raise (TypeIneq (VPre u, t)) end
  | e, t -> eqNf ctx (infer ctx e) t

and infer ctx e : value = traceInfer e; match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (u + 1)
  | ESig (t, e) -> inferTele ctx imax t e
  | EPi (t, e) -> inferTele ctx univImpl t e
  | EApp (f, x) -> let (t, g) = extPiG (infer ctx f) in
    ignore (check ctx x t); closByVal ctx t g (eval x ctx)
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (t, g) = extSigG (infer ctx e) in closByVal ctx t g (vfst (eval e ctx))
  | EAxiom (_, e) -> eval e ctx
  | EPre u -> VPre (u + 1)
  | EPathP (EPLam e) ->
    let v = eval e ctx in
    let v0 = app ctx (v, zero) in
    let v1 = app ctx (v, one) in
    let t0 = infer ctx (rbV ctx v0) in
    let t1 = infer ctx (rbV ctx v1) in
    begin match t0, t1 with
    | VKan u, VKan v ->
      if ieq u v then implv v0 (impl (rbV ctx v1) (EKan u)) ctx
      else raise (TypeIneq (VKan u, VKan v))
    | _, _ -> ExpectedFibrant (if isVSet t0 then t1 else t0) |> raise end
  | EAppFormula (f, x) ->
    check ctx x (VNt NI); let (p, _, _) = extPathP ctx f
    in app ctx (p, eval x ctx)
  | EI -> VPre 0 | EDir _ -> VNt NI
  | ENeg e ->
    if infer ctx e = VNt NI
    then VNt NI else raise (InferError e)
  | EOr (e1, e2) | EAnd (e1, e2) ->
    if infer ctx e1 = VNt NI && infer ctx e2 = VNt NI
    then VNt NI else raise (InferError e)
  | EIsOne -> implv (VNt NI) (EPre 0) ctx
  | EOneRefl -> VNt (NApp (NIsOne, one))
  | e -> raise (InferError e)

and inferTele ctx binop (p, a) b =
  let t = eval a ctx in let u = pat p in let gen = var u in
  let ctx' = upLocal (upLocal ctx p t gen) u t gen in
  let v = infer ctx' b in binop (infer ctx a) v