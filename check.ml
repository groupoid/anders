open Formula
open Error
open Trace
open Ident
open Prefs
open Expr
open Univ

let vfst : value -> value = function
  | VPair (u, _) -> u
  | v            -> VFst v

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | v            -> VSnd v

let upVar p x ctx = match p with No -> ctx | _ -> Env.add p x ctx
let upLocal (ctx : ctx) (p : name) t v : ctx = upVar p (Local, Value t, Value v) ctx
let upGlobal (ctx : ctx) (p : name) t v : ctx = upVar p (Global, Value t, Value v) ctx
let ieq u v : bool = !girard || u = v

let rec eval (e : exp) (ctx : ctx) = traceEval e; match e with
  | EKan u             -> VKan u
  | ELam (a, (p, b))   -> VLam (eval a ctx, (p, b, ctx))
  | EPi  (a, (p, b))   -> VPi  (eval a ctx, (p, b, ctx))
  | ESig (a, (p, b))   -> VSig (eval a ctx, (p, b, ctx))
  | EFst e             -> vfst (eval e ctx)
  | ESnd e             -> vsnd (eval e ctx)
  | EApp (f, x)        -> app (eval f ctx, eval x ctx)
  | EVar x             -> getRho ctx x
  | EPair (e1, e2)     -> VPair (eval e1 ctx, eval e2 ctx)
  | EHole              -> VHole
  | EPre u             -> VPre u
  | EPathP e           -> VPathP (eval e ctx)
  | EPLam e            -> VPLam (eval e ctx)
  | EPartial e         -> VPartial (eval e ctx)
  | ESystem x          -> VSystem (x, ctx)
  | EAppFormula (e, x) -> appFormula ctx e x
  | ETransp (p, i)     -> transport ctx p i
  | EId e              -> VId (eval e ctx)
  | ERef e             -> VRef (eval e ctx)
  | EJ e               -> VJ (eval e ctx)
  | EI                 -> VI
  | EDir d             -> VDir d
  | EAnd (e1, e2)      -> andFormula (eval e1 ctx, eval e2 ctx)
  | EOr (e1, e2)       -> orFormula  (eval e1 ctx, eval e2 ctx)
  | ENeg e             -> negFormula (eval e ctx)

and appFormula (ctx : ctx) (e : exp) (x : exp) = match eval e ctx with
  | VPLam f -> app (f, eval x ctx)
  | v       -> let (_, u0, u1) = extPathP ctx v in
    begin match eval x ctx with
      | VDir Zero -> u0
      | VDir One  -> u1
      | u         -> VAppFormula (v, u)
    end

and transport (ctx : ctx) (p : exp) (i : exp) = match eval i ctx with
  | VDir One -> let a = pat (name "a") in VLam (act p ezero ctx, (a, EVar a, ctx))
  | v -> VTransp (eval p ctx, v)

and closByVal t x v = let (p, e, ctx) = x in traceClos e p v;
  eval e (upLocal ctx p t v)

and app : value * value -> value = function
  | VApp (VApp (VApp (VApp (VJ _, _), _), f), _), VRef v -> f
  | VSystem (e, ctx), VRef _ ->
    eval (snd (List.find (fun (x, _) ->
      Conjunction.for_all (fun (p, d) ->
        conv ctx (getRho ctx p) (VDir d)) x) e)) ctx
  | VLam (t, f), v -> closByVal t f v
  | f, x -> VApp (f, x)

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and extPathP ctx v = match inferValue ctx v with
  | VApp (VApp (VPathP v, u0), u1) ->
    let i = pat (name "x") in let gen = EVar i in
    let ctx' = upLocal ctx i VI (Var (i, VI)) in
    (VLam (VI, (i, EAppFormula (rbV ctx v, gen), ctx')), u0, u1)
  | _ -> raise (ExpectedPath v)

and rbV ctx v : exp = traceRbV v; match v with
  | VLam (t, g)        -> rbVTele eLam ctx t g
  | VPair (u, v)       -> EPair (rbV ctx u, rbV ctx v)
  | VKan u             -> EKan u
  | VPi (t, g)         -> rbVTele ePi ctx t g
  | VSig (t, g)        -> rbVTele eSig ctx t g
  | VPre u             -> EPre u
  | VPLam f            -> EPLam (rbV ctx f)
  | Var (x, _)         -> EVar x
  | VApp (f, x)        -> EApp (rbV ctx f, rbV ctx x)
  | VFst k             -> EFst (rbV ctx k)
  | VSnd k             -> ESnd (rbV ctx k)
  | VHole              -> EHole
  | VPathP v           -> EPathP (rbV ctx v)
  | VPartial v         -> EPartial (rbV ctx v)
  | VSystem (x, ctx')  -> ESystem (List.map (fun (y, v) -> (y, rbV ctx' (eval v ctx'))) x)
  | VTransp (p, i)     -> ETransp (rbV ctx p, rbV ctx i)
  | VAppFormula (f, x) -> EAppFormula (rbV ctx f, rbV ctx x)
  | VId v              -> EId (rbV ctx v)
  | VRef v             -> ERef (rbV ctx v)
  | VJ v               -> EJ (rbV ctx v)
  | VI                 -> EI
  | VDir d             -> EDir d
  | VAnd (u, v)        -> EAnd (rbV ctx u, rbV ctx v)
  | VOr (u, v)         -> EOr (rbV ctx u, rbV ctx v)
  | VNeg u             -> ENeg (rbV ctx u)

and lookup (x : name) (ctx : ctx) = match Env.find_opt x ctx with
  | Some (_, Value v, _) -> v
  | Some (_, Exp e, _)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and rbVTele ctor ctx t g =
  let (p, _, _) = g in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  ctor p (rbV ctx t) (rbV ctx' (closByVal t g x))

and prune ctx x = match Env.find_opt x ctx with
  | Some (_, _, Exp e)   -> e
  | Some (_, _, Value v) -> rbV ctx v
  | None                 -> raise (VariableNotFound x)

and weak (e : exp) ctx = traceWeak e; match e with
  | EVar x             -> prune ctx x
  | ELam (a, (p, b))   -> weakTele eLam ctx p a b
  | EPi  (a, (p, b))   -> weakTele ePi  ctx p a b
  | ESig (a, (p, b))   -> weakTele eSig ctx p a b
  | EFst e             -> EFst (weak e ctx)
  | ESnd e             -> ESnd (weak e ctx)
  | EApp (f, x)        -> EApp (weak f ctx, weak x ctx)
  | EPair (e1, e2)     -> EPair (weak e1 ctx, weak e2 ctx)
  | EPathP u           -> EPathP (weak u ctx)
  | EPLam u            -> EPLam (weak u ctx)
  | EPartial e         -> EPartial (weak e ctx)
  | EAppFormula (f, x) -> EAppFormula (weak f ctx, weak x ctx)
  | EAnd (e1, e2)      -> EAnd (weak e1 ctx, weak e2 ctx)
  | EOr (e1, e2)       -> EOr (weak e1 ctx, weak e2 ctx)
  | ENeg e             -> ENeg (weak e ctx)
  | EId e              -> EId (weak e ctx)
  | ERef e             -> ERef (weak e ctx)
  | EJ e               -> EJ (weak e ctx)
  | e                  -> e

and weakTele ctor ctx p a b : exp =
  let t = weak a ctx in
    ctor p t (weak b (upVar p (Local, Exp t, Exp (EVar p)) ctx))

and conv ctx v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (a, b), VPair (c, d) -> conv ctx a c && conv ctx b d
    | VPair (a, b), v | v, VPair (a, b) -> conv ctx (vfst v) a && conv ctx (vsnd v) b
    | VPi (a, g), VPi (b, h) | VSig (a, g), VSig (b, h)
    | VLam (a, g), VLam (b, h) ->
      let (p, e1, ctx1) = g in let (q, e2, ctx2) = h in
      conv ctx a b &&
        (weak e1 (upLocal ctx1 p a (Var (p, a))) =
         weak e2 (upLocal ctx2 q b (Var (q, b))) ||
         let x = Var (p, a) in let ctx' = upLocal ctx p a x in
          conv ctx' (closByVal a g x) (closByVal a h x))
    | VLam (a, (p, e, v)), b | b, VLam (a, (p, e, v)) ->
      let x = Var (p, a) in let ctx' = upLocal ctx p a x in
      conv ctx' (app (b, x)) (closByVal a (p, e, v) x)
    | VPre u, VPre v -> ieq u v
    | VPLam f, VPLam g -> conv ctx f g
    | VPLam f, v | v, VPLam f -> let p = pat (name "x") in
      let i = Var (p, VI) in let ctx' = upLocal ctx p VI i in
      conv ctx' (act (rbV ctx' v) (EVar p) ctx') (app (f, i))
    | Var (u, _), Var (v, _) -> u = v
    | VApp (f, a), VApp (g, b) -> conv ctx f g && conv ctx a b
    | VFst x, VFst y | VSnd x, VSnd y -> conv ctx x y
    | VPathP a, VPathP b -> conv ctx a b
    | VPartial a, VPartial b -> conv ctx a b
    | VAppFormula (f, x), VAppFormula (g, y) -> conv ctx f g && conv ctx x y
    | VTransp (p, i), VTransp (q, j) -> conv ctx p q && conv ctx i j
    | VOr _, VOr _ -> orEq v1 v2
    | VAnd _, VAnd _ -> andEq v1 v2
    | VNeg x, VNeg y -> conv ctx x y
    | VI, VI -> true
    | VDir u, VDir v -> u = v
    | VId u, VId v -> conv ctx u v
    | VJ u, VJ v -> conv ctx u v
    | _, _ -> false
  end || convId ctx v1 v2

and convId ctx v1 v2 =
  (* Id A a b is proof-irrelevant *)
  match inferValue ctx v1, inferValue ctx v2 with
  | VApp (VApp (VId t1, a1), b1), VApp (VApp (VId t2, a2), b2) ->
    conv ctx t1 t2 && conv ctx a1 a2 && conv ctx b1 b2
  | _, _ -> false

and eqNf ctx v1 v2 : unit = traceEqNF v1 v2;
  if conv ctx v1 v2 then () else raise (TypeIneq (v1, v2))

and check ctx (e0 : exp) (t0 : value) =
  traceCheck e0 t0; match e0, t0 with
  | ELam (a, (p, b)), VPi (t, g) ->
    eqNf ctx (eval a ctx) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in
    check ctx' b (closByVal t g x)
  | EPair (e1, e2), VSig (t, g) -> check ctx e1 t;
    check ctx e2 (closByVal t g (eval e1 ctx))
  | EHole, v -> traceHole v ctx
  | e, VApp (VApp (VPathP p, u0), u1) ->
    let v0 = act e ezero ctx in
    let v1 = act e eone  ctx in
    let i = pat (name "x") in let gen = EVar i in
    let ctx' = upLocal ctx i VI (Var (i, VI)) in
    check ctx' (rbV ctx' (act e gen ctx')) (act (rbV ctx p) gen ctx');
    eqNf ctx v0 u0; eqNf ctx v1 u1
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (TypeIneq (VPre u, VPre v))
    | t -> raise (TypeIneq (VPre u, t)) end
  | ESystem x, VApp (VPartial v, i) ->
    eqNf ctx (eval (getFormula x) ctx) i;
    List.iter (fun (_, e) -> check ctx e v) x;
    (* check overlapping cases *)
    List.iter (fun (x1, e1) ->
      List.iter (fun (x2, e2) ->
        if not (Conjunction.disjoint x1 x2) then
          eqNf ctx (eval e1 ctx) (eval e2 ctx)) x) x
  | e, t -> eqNf ctx (infer ctx e) t

and infer ctx e : value = traceInfer e; match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (u + 1)
  | ESig (a, (p, b)) -> inferTele ctx imax p a b
  | EPi (a, (p, b)) -> inferTele ctx univImpl p a b
  | ELam (a, (p, b)) -> inferLam ctx p a e
  | EApp (f, x) -> let (t, g) = extPiG ctx (infer ctx f) in check ctx x t; closByVal t g (eval x ctx)
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (t, g) = extSigG (infer ctx e) in closByVal t g (vfst (eval e ctx))
  | EPre u -> VPre (u + 1)
  | EPathP p -> inferPath ctx p
  | EPartial e -> let n = extSet (infer ctx e) in implv VI (EPre n) ctx
  | EAppFormula (f, x) -> check ctx x VI; let (p, _, _) = extPathP ctx (eval f ctx) in app (p, eval x ctx)
  | ETransp (p, i) -> inferTransport ctx p i
  | EI -> VPre 0 | EDir _ -> VI
  | ENeg e -> check ctx e VI; VI
  | EOr (e1, e2) | EAnd (e1, e2) -> check ctx e1 VI; check ctx e2 VI; VI
  | EId e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (impl e (EPre n)) ctx
  | ERef e -> let v = eval e ctx in let t = infer ctx e in VApp (VApp (VId t, v), v)
  | EJ e -> inferJ ctx e
  | e -> raise (InferError e)

and inferLam ctx p a e =
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in VPi (t, (p, rbV ctx' (infer ctx' e), ctx))

and inferJ ctx e =
  let n = extSet (infer ctx e) in let x = name "x" in let y = name "y" in
  let pi = name "P" in let p = name "p" in let id = EApp (EApp (EId e, EVar x), EVar y) in
  VPi (eval (EPi (e, (x, EPi (e, (y, impl id (EPre n)))))) ctx,
        (pi, EPi (e, (x, impl (EApp (EApp (EApp (EVar pi, EVar x), EVar x), ERef (EVar x)))
          (EPi (e, (y, EPi (id, (p, EApp (EApp (EApp (EVar pi, EVar x), EVar y), EVar p)))))))), ctx))

and inferValue ctx = function
  | Var (_, t)         -> t
  | VFst e             -> fst (extSigG (inferValue ctx e))
  | VSnd e             -> let (t, g) = extSigG (inferValue ctx e) in closByVal t g (VFst e)
  | VApp (f, x)        -> let (t, g) = extPiG ctx (inferValue ctx f) in closByVal t g x
  | VAppFormula (f, x) -> let (p, _, _) = extPathP ctx f in app (p, x)
  | VRef v             -> VApp (VApp (VId (inferValue ctx v), v), v)
  | v                  -> infer ctx (rbV ctx v)

and inferPath (ctx : ctx) (p : exp) =
  let v0 = act p ezero ctx in
  let v1 = act p eone  ctx in
  let t0 = inferValue ctx v0 in
  let t1 = inferValue ctx v1 in
  begin match t0, t1 with
    | VKan u, VKan v ->
      if ieq u v then implv v0 (impl (rbV ctx v1) (EKan u)) ctx
      else raise (TypeIneq (VKan u, VKan v))
    | _, _ -> ExpectedFibrant (if isSet t0 then t1 else t0) |> raise
  end

and inferTransport (ctx : ctx) (p : exp) (i : exp) =
  check ctx i VI;
  let u0 = act p ezero ctx in
  let u1 = act p eone  ctx in
  let x = pat (name "x") in let gen = EVar x in
  let ctx' = upLocal ctx x VI (Var (x, VI)) in
  begin match inferValue ctx' (act p gen ctx') with
    | VKan _ -> ()
    | v      -> raise (ExpectedFibrant v)
  end;
  List.iter (fun phi ->
    let ctx'' = faceEnv phi ctx' in
    eqNf ctx'' u0 (act p gen ctx''))
    (solve (eval i ctx) One);
  implv u0 (rbV ctx u1) ctx

and inferTele ctx binop p a b =
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in binop (infer ctx a) v

and act e i ctx = eval (EAppFormula (e, i)) ctx

and extPiG ctx : value -> value * clos = function
  | VApp (VPartial t, i) -> (VApp (VApp (VId VI, VDir One), i), (No, rbV ctx t, ctx))
  | VPi (t, g) -> (t, g)
  | u -> raise (ExpectedPi u)
