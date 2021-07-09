open Formula
open Error
open Trace
open Ident
open Prefs
open Elab
open Expr

let freshDim () = let i = fresh (name "ι") in (i, EVar i, Var (i, VI))

let vfst : value -> value = function
  | VPair (u, _) -> u
  | v            -> VFst v

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | v            -> VSnd v

let upVar p x ctx = match p with Irrefutable -> ctx | _ -> Env.add p x ctx
let upLocal (ctx : ctx) (p : name) t v : ctx = upVar p (Local, Value t, Value v) ctx
let upGlobal (ctx : ctx) (p : name) t v : ctx = upVar p (Global, Value t, Value v) ctx
let ieq u v : bool = !girard || u = v

(* Evaluator *)
let rec eval (e : exp) (ctx : ctx) = traceEval e; match e with
  | EPre u             -> VPre u
  | EKan u             -> VKan u
  | EVar x             -> getRho ctx x
  | EHole              -> VHole
  | EPi  (a, (p, b))   -> VPi (eval a ctx, (p, b, ctx))
  | ELam (a, (p, b))   -> VLam (eval a ctx, (p, b, ctx))
  | EApp (f, x)        -> app (eval f ctx, eval x ctx)
  | ESig (a, (p, b))   -> VSig (eval a ctx, (p, b, ctx))
  | EPair (e1, e2)     -> VPair (eval e1 ctx, eval e2 ctx)
  | EFst e             -> vfst (eval e ctx)
  | ESnd e             -> vsnd (eval e ctx)
  | EId e              -> VId (eval e ctx)
  | ERef e             -> VRef (eval e ctx)
  | EJ e               -> VJ (eval e ctx)
  | EPathP e           -> VPathP (eval e ctx)
  | EPLam e            -> VPLam (eval e ctx)
  | EAppFormula (e, x) -> appFormula (eval e ctx) (eval x ctx)
  | EI                 -> VI
  | EDir d             -> VDir d
  | EAnd (e1, e2)      -> andFormula (eval e1 ctx, eval e2 ctx)
  | EOr (e1, e2)       -> orFormula (eval e1 ctx, eval e2 ctx)
  | ENeg e             -> negFormula (eval e ctx)
  | ETransp (p, i)     -> transport ctx p i
  | EPartial e         -> VPartial (eval e ctx)
  | ESystem x          -> VSystem (x, ctx)
  | ESub (a, i, u)     -> VSub (eval a ctx, eval i ctx, eval u ctx)

and appFormula v x = match v with
  | VPLam f -> app (f, x)
  | _       -> let (_, u0, u1) = extPathP (inferV v) in
    begin match x with
      | VDir Zero -> u0
      | VDir One  -> u1
      | i         -> VAppFormula (v, i)
    end

and transport (ctx : ctx) (p : exp) (i : exp) = match eval i ctx with
  | VDir One -> let a = fresh (name "a") in VLam (act p ezero ctx, (a, EVar a, ctx))
  | v        -> VTransp (eval p ctx, v)

and closByVal t x v = let (p, e, ctx) = x in traceClos e p v;
  eval e (upLocal ctx p t v)

and app : value * value -> value = function
  | VApp (VApp (VApp (VApp (VJ _, _), _), f), _), VRef _ -> f
  | VSystem (Split xs, ctx), _ -> eval (reduceSystem ctx xs) ctx
  | VSystem (Const x, ctx), _ -> eval x ctx
  | VLam (t, f), v -> closByVal t f v
  | f, x -> VApp (f, x)

and reduceSystem ctx xs =
  snd (List.find (fun (x, _) ->
    Conjunction.for_all (fun (p, d) ->
      conv (getRho ctx p) (VDir d)) x) xs)

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and act e i ctx = eval (EAppFormula (e, i)) ctx

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | Var (_, t)               -> t
  | VFst e                   -> fst (extSigG (inferV e))
  | VSnd e                   -> let (t, g) = extSigG (inferV e) in closByVal t g (VFst e)
  | VApp (VTransp (p, _), _) -> appFormula p vone
  | VApp (f, x)              -> begin match inferV f with
    | VApp (VPartial t, _) -> t
    | VPi (t, g) -> closByVal t g x
    | v -> raise (ExpectedPi v)
  end
  | VAppFormula (f, x)       -> let (p, _, _) = extPathP (inferV f) in appFormula p x
  | VRef v                   -> VApp (VApp (VId (inferV v), v), v)
  | VPre n                   -> VPre (n + 1)
  | VKan n                   -> VKan (n + 1)
  | VI                       -> VPre 0
  | VDir _ | VOr _ | VAnd _  -> VI
  | VSig (a, (p, e, rho))    -> imax (inferV a) (infer (upLocal rho p a (Var (p, a))) e)
  | VPi  (a, (p, e, rho))    -> univImpl (inferV a) (infer (upLocal rho p a (Var (p, a))) e)
  | v                        -> raise (ExpectedNeutral v)

(* Readback *)
and rbV v : exp = traceRbV v; match v with
  | VLam (t, g)             -> rbVTele eLam t g
  | VPair (u, v)            -> EPair (rbV u, rbV v)
  | VKan u                  -> EKan u
  | VPi (t, g)              -> rbVTele ePi t g
  | VSig (t, g)             -> rbVTele eSig t g
  | VPre u                  -> EPre u
  | VPLam f                 -> EPLam (rbV f)
  | Var (x, _)              -> EVar x
  | VApp (f, x)             -> EApp (rbV f, rbV x)
  | VFst k                  -> EFst (rbV k)
  | VSnd k                  -> ESnd (rbV k)
  | VHole                   -> EHole
  | VPathP v                -> EPathP (rbV v)
  | VPartial v              -> EPartial (rbV v)
  | VSystem (Split xs, ctx) -> ESystem (Split (List.map (fun (y, v) -> (y, rbV (eval v ctx))) xs))
  | VSystem (Const x, ctx)  -> ESystem (Const (rbV (eval x ctx)))
  | VSub (a, i, u)          -> ESub (rbV a, rbV i, rbV u)
  | VTransp (p, i)          -> ETransp (rbV p, rbV i)
  | VAppFormula (f, x)      -> EAppFormula (rbV f, rbV x)
  | VId v                   -> EId (rbV v)
  | VRef v                  -> ERef (rbV v)
  | VJ v                    -> EJ (rbV v)
  | VI                      -> EI
  | VDir d                  -> EDir d
  | VAnd (u, v)             -> EAnd (rbV u, rbV v)
  | VOr (u, v)              -> EOr (rbV u, rbV v)
  | VNeg u                  -> ENeg (rbV u)

and rbVTele ctor t g =
  let (p, _, _) = g in let x = Var (p, t) in
  ctor p (rbV t) (rbV (closByVal t g x))

and prune ctx x = match Env.find_opt x ctx with
  | Some (_, _, Exp e)   -> e
  | Some (_, _, Value v) -> rbV v
  | None                 -> raise (VariableNotFound x)

(* Weak *)
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

(* Convertibility *)
and conv v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (a, b), VPair (c, d) -> conv a c && conv b d
    | VPair (a, b), v | v, VPair (a, b) -> conv (vfst v) a && conv (vsnd v) b
    | VPi (a, g), VPi (b, h) | VSig (a, g), VSig (b, h)
    | VLam (a, g), VLam (b, h) ->
      let (p, e1, ctx1) = g in let (q, e2, ctx2) = h in
      let x = Var (p, a) in conv a b &&
        (weak e1 (upLocal ctx1 p a (Var (p, a))) =
         weak e2 (upLocal ctx2 q b (Var (q, b))) ||
         conv (closByVal a g x) (closByVal a h x))
    | VLam (a, (p, e, v)), b | b, VLam (a, (p, e, v)) ->
      let x = Var (p, a) in conv (app (b, x)) (closByVal a (p, e, v) x)
    | VPre u, VPre v -> ieq u v
    | VPLam f, VPLam g -> conv f g
    | VPLam f, v | v, VPLam f -> let (_, _, i) = freshDim () in conv (appFormula v i) (app (f, i))
    | Var (u, _), Var (v, _) -> u = v
    | VApp (f, a), VApp (g, b) -> conv f g && conv a b
    | VFst x, VFst y | VSnd x, VSnd y -> conv x y
    | VPathP a, VPathP b -> conv a b
    | VPartial a, VPartial b -> conv a b
    | VAppFormula (f, x), VAppFormula (g, y) -> conv f g && conv x y
    | VSystem (Split xs, ctx1), VSystem (Split ys, ctx2) ->
      let xs' = List.map (fun (p, e) -> (p, eval e ctx1)) xs in
      let ys' = List.map (fun (p, e) -> (p, eval e ctx2)) ys in
      systemSubset xs' ctx1 ys' ctx2 && systemSubset ys' ctx2 xs' ctx1
    | VSystem (Const x, ctx1), VSystem (Const y, ctx2) ->
      conv (eval x ctx1) (eval y ctx2)
    | VSystem (Const x, ctx), VSystem (Split xs, ctx')
    | VSystem (Split xs, ctx'), VSystem (Const x, ctx) ->
      let v = eval x ctx in List.for_all (fun (_, y) -> conv (eval y ctx') v) xs
    | VTransp (p, i), VTransp (q, j) -> conv p q && conv i j
    | VOr _, VOr _ -> orEq v1 v2
    | VAnd _, VAnd _ -> andEq v1 v2
    | VNeg x, VNeg y -> conv x y
    | VI, VI -> true
    | VDir u, VDir v -> u = v
    | VId u, VId v -> conv u v
    | VJ u, VJ v -> conv u v
    | _, _ -> false
  end || convId v1 v2

and faceSubset phi ctx1 psi ctx2 =
  let xs = Conjunction.elements phi in
  let ys = Conjunction.elements psi in
  List.for_all (fun (p, x) ->
    let v = getRho ctx1 p in
    List.exists (fun (q, y) ->
      x = y && conv v (getRho ctx2 q)) ys) xs

and faceConv phi ctx1 psi ctx2 =
  faceSubset phi ctx1 psi ctx2 && faceSubset psi ctx2 phi ctx1

and systemSubset xs ctx1 ys ctx2 =
  List.for_all (fun (p, x) ->
    List.exists (fun (q, y) ->
      conv x y && faceConv p ctx1 q ctx2) ys) xs

and convId v1 v2 =
  (* Id A a b is proof-irrelevant *)
  try match inferV v1, inferV v2 with
    | VApp (VApp (VId t1, a1), b1), VApp (VApp (VId t2, a2), b2) ->
      conv t1 t2 && conv a1 a2 && conv b1 b2
    | _, _ -> false
  with ExpectedNeutral _ -> false

and eqNf v1 v2 : unit = traceEqNF v1 v2;
  if conv v1 v2 then () else raise (TypeIneq (v1, v2))

(* Type checker itself *)
and lookup (x : name) (ctx : ctx) = match Env.find_opt x ctx with
  | Some (_, Value v, _) -> v
  | Some (_, Exp e, _)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and check ctx (e0 : exp) (t0 : value) =
  traceCheck e0 t0; match e0, t0 with
  | ELam (a, (p, b)), VPi (t, g) ->
    eqNf (eval a ctx) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in
    check ctx' b (closByVal t g x)
  | EPair (e1, e2), VSig (t, g) -> check ctx e1 t;
    check ctx e2 (closByVal t g (eval e1 ctx))
  | EHole, v -> traceHole v ctx
  | e, VApp (VApp (VPathP p, u0), u1) ->
    let v0 = act e ezero ctx in
    let v1 = act e eone  ctx in
    let (i, x, v) = freshDim () in let ctx' = upLocal ctx i VI v in
    check ctx' (rbV (act e x ctx')) (appFormula p v);
    eqNf v0 u0; eqNf v1 u1
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (TypeIneq (VPre u, VPre v))
    | t -> raise (TypeIneq (VPre u, t)) end
  | ESystem (Split xs), VApp (VPartial t, i) ->
    eqNf (eval (getFormula xs) ctx) i;
    List.iter (fun (_, e) -> check ctx e t) xs;
    (* check overlapping cases *)
    List.iter (fun (x1, e1) ->
      List.iter (fun (x2, e2) ->
        if not (Conjunction.disjoint x1 x2) then
          eqNf (eval e1 ctx) (eval e2 ctx)) xs) xs
  | ESystem (Const x), VApp (VPartial t, _) -> check ctx x t
  | e, t -> eqNf (infer ctx e) t

and infer ctx e : value = traceInfer e; match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (u + 1)
  | ESig (a, (p, b)) -> inferTele ctx imax p a b
  | EPi (a, (p, b)) -> inferTele ctx univImpl p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EApp (f, x) -> begin match infer ctx f with
    | VApp (VPartial t, i) -> check ctx x (VApp (VApp (VId VI, VDir One), i)); t
    | VPi (t, g) -> check ctx x t; closByVal t g (eval x ctx)
    | v -> raise (ExpectedPi v)
  end
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (t, g) = extSigG (infer ctx e) in closByVal t g (vfst (eval e ctx))
  | EPre u -> VPre (u + 1)
  | EPathP p -> inferPath ctx p
  | EPartial e -> let n = extSet (infer ctx e) in implv VI (EPre n) ctx
  | EAppFormula (f, x) -> check ctx x VI; let (p, _, _) = extPathP (infer ctx (rbV (eval f ctx))) in
    appFormula p (eval x ctx)
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
  let ctx' = upLocal ctx p t x in VPi (t, (p, rbV (infer ctx' e), ctx))

and inferJ ctx e =
  let n = extSet (infer ctx e) in let x = name "x" in let y = name "y" in
  let pi = name "P" in let p = name "p" in let id = EApp (EApp (EId e, EVar x), EVar y) in
  VPi (eval (EPi (e, (x, EPi (e, (y, impl id (EPre n)))))) ctx,
        (pi, EPi (e, (x, impl (EApp (EApp (EApp (EVar pi, EVar x), EVar x), ERef (EVar x)))
          (EPi (e, (y, EPi (id, (p, EApp (EApp (EApp (EVar pi, EVar x), EVar y), EVar p)))))))), ctx))

and inferPath (ctx : ctx) (p : exp) =
  let (i, x, v) = freshDim () in let ctx' = upLocal ctx i VI v in
  let t = infer ctx' (rbV (act p x ctx')) in ignore (extSet t);

  let v0 = act p ezero ctx in let v1 = act p eone ctx in
  implv v0 (impl (rbV v1) (rbV t)) ctx

and inferTransport (ctx : ctx) (p : exp) (i : exp) =
  check ctx i VI;
  let u0 = act p ezero ctx in
  let u1 = act p eone  ctx in

  let (j, x, v) = freshDim () in let ctx' = upLocal ctx j VI v in
  ignore (extKan (infer ctx' (rbV (act p x ctx'))));

  (* Check that p is constant at i = 1 *)
  List.iter (fun phi ->
    let rho = faceEnv phi ctx' in
    eqNf (act p ezero rho) (act p x rho))
    (solve (eval i ctx) One);
  implv u0 (rbV u1) ctx

and inferTele ctx binop p a b =
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in binop (infer ctx a) v
