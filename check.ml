open Formula
open Prelude
open Error
open Trace
open Ident
open Elab
open Expr

let freshDim () = let i = freshName "ι" in (i, EVar i, Var (i, VI))

let ieq u v : bool = !Prefs.girard || u = v
let vfst : value -> value = function
  | VPair (_, u, _) -> u
  | v               -> VFst v

let vsnd : value -> value = function
  | VPair (_, _, u) -> u
  | v               -> VSnd v

(* Evaluator *)
let rec eval (e0 : exp) (ctx : ctx) = traceEval e0; match e0 with
  | EPre u             -> VPre u
  | EKan u             -> VKan u
  | EVar x             -> getRho ctx x
  | EHole              -> VHole
  | EPi  (a, (p, b))   -> let t = eval a ctx in VPi (t, (p, closByVal ctx p t b))
  | ESig (a, (p, b))   -> let t = eval a ctx in VSig (t, (p, closByVal ctx p t b))
  | ELam (a, (p, b))   -> let t = eval a ctx in VLam (t, (p, closByVal ctx p t b))
  | EApp (f, x)        -> app (eval f ctx, eval x ctx)
  | EPair (r, e1, e2)  -> VPair (r, eval e1 ctx, eval e2 ctx)
  | EFst e             -> vfst (eval e ctx)
  | ESnd e             -> vsnd (eval e ctx)
  | EField (e, p)      -> evalField p (eval e ctx)
  | EId e              -> VId (eval e ctx)
  | ERef e             -> VRef (eval e ctx)
  | EJ e               -> VJ (eval e ctx)
  | EPathP e           -> VPathP (eval e ctx)
  | EPLam e            -> VPLam (eval e ctx)
  | EAppFormula (e, x) -> appFormula (eval e ctx) (eval x ctx)
  | EI                 -> VI
  | EDir d             -> VDir d
  | EAnd (e1, e2)      -> evalAnd (eval e1 ctx) (eval e2 ctx)
  | EOr (e1, e2)       -> evalOr (eval e1 ctx) (eval e2 ctx)
  | ENeg e             -> negFormula (eval e ctx)
  | ETransp (p, i)     -> transport ctx p i
  | EHComp e           -> VHComp (eval e ctx)
  | EPartial e         -> VPartial (eval e ctx)
  | ESystem xs         -> VSystem (evalSystem ctx xs)
  | ESub (a, i, u)     -> VSub (eval a ctx, eval i ctx, eval u ctx)
  | EInc e             -> begin match eval e ctx with VOuc v -> v | v -> VInc v end
  | EOuc e             -> begin match eval e ctx with VInc x -> x | v -> evalOuc ctx v end

and appFormula v x = match v with
  | VPLam f -> app (f, x)
  | _       -> let (_, u0, u1) = extPathP (inferV v) in
    begin match x with
      | VDir Zero -> u0
      | VDir One  -> u1
      | i         -> VAppFormula (v, i)
    end

and transport (ctx : ctx) (p : exp) (i : exp) = match eval i ctx with
  | VDir One -> let a = fresh (name "a") in VLam (act p ezero ctx, (a, fun x -> x))
  | v        -> VTransp (eval p ctx, v)

and closByVal ctx p t e v = traceClos e p v;
  (* dirty hack to handle free variables introduced by type checker,
     for example, while checking terms like p : Path P a b *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and app : value * value -> value = function
  | VApp (VApp (VApp (VApp (VJ _, _), _), f), _), VRef _ -> f
  | VApp (VApp (VHComp _, VDir One), f), _ -> app (app (f, vone), VRef vone)
  | VSystem ts, x -> reduceSystem ts x
  | VLam (_, (_, f)), v -> f v
  | f, x -> VApp (f, x)

and evalSystem ctx ts =
  let ts' =
    System.fold (fun alpha talpha ->
      Env.bindings alpha
      |> List.rev_map (fun (i, d) -> solve (getRho ctx i) d)
      |> meetss
      |> List.rev_map (fun beta -> (beta, eval talpha (faceEnv beta ctx)))
      |> List.rev_append) ts [] in

  (* ensure incomparability *)
  List.filter (fun (alpha, _) ->
    List.for_all (fun (beta, _) ->
      not (lt beta alpha)) ts') ts'
  |> mkSystem

and reduceSystem ts x =
  match System.find_opt eps ts with
  | Some v -> v
  | None   -> VApp (VSystem ts, x)

and evalOuc ctx v = match inferV v with
  | VSub (_, i, f) ->
    begin match eval (rbV i) ctx with
      | VDir One -> app (eval (rbV f) ctx, VRef vone)
      | _        -> VOuc v
    end
  | _ -> VOuc v

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and act e i ctx = eval (EAppFormula (e, i)) ctx

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | VPi (t, (x, f)) | VSig (t, (x, f)) -> imax (inferV t) (inferV (f (Var (x, t))))
  | VLam (t, (x, f)) -> VPi (t, (x, fun x -> inferV (f x)))
  | Var (_, t)               -> t
  | VFst e                   -> fst (extSigG (inferV e))
  | VSnd e                   -> let (_, (_, g)) = extSigG (inferV e) in g (vfst e)
  | VApp (VTransp (p, _), _) -> appFormula p vone
  | VApp (VApp (VApp (VHComp t, _), _), _) -> t
  | VApp (f, x)              -> begin match inferV f with
    | VApp (VPartial t, _) -> t
    | VPi (_, (_, g)) -> g x
    | v -> raise (ExpectedPi v)
  end
  | VAppFormula (f, x)       -> let (p, _, _) = extPathP (inferV f) in appFormula p x
  | VRef v                   -> VApp (VApp (VId (inferV v), v), v)
  | VPre n                   -> VPre (n + 1)
  | VKan n                   -> VKan (n + 1)
  | VI                       -> VPre 0
  | VOuc v                   -> begin match inferV v with
    | VSub (t, _, _) -> t
    | _ -> raise (ExpectedSubtype (rbV v))
  end
  | VId v -> let n = extSet (inferV v) in implv v (implv v (VPre n))
  | VJ v -> inferJ v (inferV v)
  | VPathP p -> let (_, _, v) = freshDim () in let t = inferV (appFormula p v) in
    let v0 = appFormula p vzero in let v1 = appFormula p vone in implv v0 (implv v1 t)
  | VDir _ | VOr _ | VAnd _ | VNeg _ -> VI
  | VTransp (p, _) -> implv (appFormula p vzero) (appFormula p vone)
  | VHComp v -> inferHComp v
  | VSub (a, _, _) -> VPre (extSet (inferV a))
  | VPartial v -> let n = extSet (inferV v) in implv VI (VPre n)
  | v                        -> raise (ExpectedNeutral v)

and extByTag p : value -> value option = function
  | VPair (t, fst, snd) -> begin match !t with
    | Some q -> if p = q then Some fst else extByTag p snd
    | _      -> extByTag p snd
  end | _ -> None

and evalField p v =
  match extByTag p v with
  | Some k -> k | None -> begin match inferV v with
    | VSig (_, (q, _)) -> if matchIdent p q then vfst v else evalField p (vsnd v)
    | t -> raise (ExpectedSig t)
  end

and upd e = function
  | VLam (t, (x, g))   -> VLam (upd e t, (x, g >> upd e))
  | VPair (r, u, v)    -> VPair (r, upd e u, upd e v)
  | VKan u             -> VKan u
  | VPi (t, (x, g))    -> VPi (upd e t, (x, g >> upd e))
  | VSig (t, (x, g))   -> VSig (upd e t, (x, g >> upd e))
  | VPre u             -> VPre u
  | VPLam f            -> VPLam (upd e f)
  | Var (i, VI)        ->
    begin match Env.find_opt i e with
      | Some d -> VDir d
      | None   -> Var (i, VI)
    end
  | Var (x, v)         -> Var (x, v)
  | VApp (f, x)        -> VApp (upd e f, upd e x)
  | VFst k             -> VFst (upd e k)
  | VSnd k             -> VSnd (upd e k)
  | VHole              -> VHole
  | VPathP v           -> VPathP (upd e v)
  | VPartial v         -> VPartial (upd e v)
  | VSystem ts         ->
    VSystem (System.bindings ts
            |> List.filter_map (fun (e', v) ->
              if compatible e e' then
                Some (Env.filter (fun k _ -> not (Env.mem k e)) e', upd e v)
              else None)
            |> mkSystem)
  | VSub (a, i, u)     -> VSub (upd e a, upd e i, upd e u)
  | VTransp (p, i)     -> VTransp (upd e p, upd e i)
  | VHComp v           -> VHComp (upd e v)
  | VAppFormula (f, x) -> VAppFormula (upd e f, upd e x)
  | VId v              -> VId (upd e v)
  | VRef v             -> VRef (upd e v)
  | VJ v               -> VJ (upd e v)
  | VI                 -> VI
  | VDir d             -> VDir d
  | VAnd (u, v)        -> andFormula (upd e u, upd e v)
  | VOr (u, v)         -> orFormula (upd e u, upd e v)
  | VNeg u             -> negFormula (upd e u)
  | VInc v             -> VInc (upd e v)
  | VOuc v             -> VOuc (upd e v)

and updTerm alpha = function
  | Exp e   -> Exp e
  | Value v -> Value (upd alpha v)

and faceEnv alpha ctx =
  Env.map (fun (p, t, v) -> (p, updTerm alpha t, updTerm alpha v)) ctx
  |> Env.fold (fun p dir -> Env.add p (Local, Value VI, Value (VDir dir))) alpha

(* Readback *)
and rbV v : exp = traceRbV v; match v with
  | VLam (t, g)        -> rbVTele eLam t g
  | VPair (r, u, v)    -> EPair (r, rbV u, rbV v)
  | VKan u             -> EKan u
  | VPi (t, g)         -> rbVTele ePi t g
  | VSig (t, g)        -> rbVTele eSig t g
  | VPre u             -> EPre u
  | VPLam f            -> EPLam (rbV f)
  | Var (x, _)         -> EVar x
  | VApp (f, x)        -> EApp (rbV f, rbV x)
  | VFst k             -> EFst (rbV k)
  | VSnd k             -> ESnd (rbV k)
  | VHole              -> EHole
  | VPathP v           -> EPathP (rbV v)
  | VPartial v         -> EPartial (rbV v)
  | VSystem ts         -> ESystem (System.map rbV ts)
  | VSub (a, i, u)     -> ESub (rbV a, rbV i, rbV u)
  | VTransp (p, i)     -> ETransp (rbV p, rbV i)
  | VHComp v           -> EHComp (rbV v)
  | VAppFormula (f, x) -> EAppFormula (rbV f, rbV x)
  | VId v              -> EId (rbV v)
  | VRef v             -> ERef (rbV v)
  | VJ v               -> EJ (rbV v)
  | VI                 -> EI
  | VDir d             -> EDir d
  | VAnd (u, v)        -> EAnd (rbV u, rbV v)
  | VOr (u, v)         -> EOr (rbV u, rbV v)
  | VNeg u             -> ENeg (rbV u)
  | VInc v             -> EInc (rbV v)
  | VOuc v             -> EOuc (rbV v)

and rbVTele ctor t (p, g) = let x = Var (p, t) in ctor p (rbV t) (rbV (g x))

and prune ctx x = match Env.find_opt x ctx with
  | Some (_, _, Exp e)   -> e
  | Some (_, _, Value v) -> rbV v
  | None                 -> raise (VariableNotFound x)

(* Convertibility *)
and conv v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (_, a, b), VPair (_, c, d) -> conv a c && conv b d
    | VPair (_, a, b), v | v, VPair (_, a, b) -> conv (vfst v) a && conv (vsnd v) b
    | VPi  (a, (p, f)), VPi  (b, (_, g))
    | VSig (a, (p, f)), VSig (b, (_, g))
    | VLam (a, (p, f)), VLam (b, (_, g)) ->
      let x = Var (p, a) in conv a b && conv (f x) (g x)
    | VLam (a, (p, f)), b | b, VLam (a, (p, f)) ->
      let x = Var (p, a) in conv (app (b, x)) (f x)
    | VPre u, VPre v -> ieq u v
    | VPLam f, VPLam g -> conv f g
    | VPLam f, v | v, VPLam f -> let (_, _, i) = freshDim () in conv (appFormula v i) (app (f, i))
    | Var (u, _), Var (v, _) -> u = v
    | VApp (f, a), VApp (g, b) -> conv f g && conv a b
    | VFst x, VFst y | VSnd x, VSnd y -> conv x y
    | VPathP a, VPathP b -> conv a b
    | VPartial a, VPartial b -> conv a b
    | VAppFormula (f, x), VAppFormula (g, y) -> conv f g && conv x y
    | VSystem xs, VSystem ys -> keys xs = keys ys && System.for_all (fun _ b -> b) (intersectionWith conv xs ys)
    | VTransp (p, i), VTransp (q, j) -> conv p q && conv i j
    | VHComp a, VHComp b -> conv a b
    | VSub (a, i, u), VSub (b, j, v) -> conv a b && conv i j && conv u v
    | VOr (x, y), VDir Zero | VAnd (x, y), VDir One  -> conv x v2 && conv y v2
    | VOr (x, y), VDir One  | VAnd (x, y), VDir Zero -> conv x v2 || conv y v2
    | VOr _,  _ | _, VOr _  -> orEq v1 v2
    | VAnd _, _ | _, VAnd _ -> andEq v1 v2
    | VNeg x, VNeg y -> conv x y
    | VI, VI -> true
    | VDir u, VDir v -> u = v
    | VId u, VId v | VJ u, VJ v -> conv u v
    | VInc u, VInc v | VOuc u, VOuc v -> conv u v
    | _, _ -> false
  end || convId v1 v2

and faceSubset phi psi =
  List.for_all (fun (_, x) -> List.exists (fun (_, y) -> conv x y) psi) phi
and faceConv phi psi = faceSubset phi psi && faceSubset psi phi

and systemSubset xs ys =
  List.for_all (fun (p, x) -> List.exists (fun (q, y) ->
    faceConv p q && conv (extFace p x) (extFace q y)) ys) xs

and convId v1 v2 =
  (* Id A a b is proof-irrelevant *)
  try match inferV v1, inferV v2 with
    | VApp (VApp (VId t1, a1), b1), VApp (VApp (VId t2, a2), b2) ->
      conv t1 t2 && conv a1 a2 && conv b1 b2
    | _, _ -> false
  with ExpectedNeutral _ -> false

and eqNf v1 v2 : unit = traceEqNF v1 v2;
  if conv v1 v2 then () else raise (Ineq (v1, v2))

(* Type checker itself *)
and lookup (x : name) (ctx : ctx) = match Env.find_opt x ctx with
  | Some (_, Value v, _) -> v
  | Some (_, Exp e, _)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and check ctx (e0 : exp) (t0 : value) =
  traceCheck e0 t0; try match e0, t0 with
  | ELam (a, (p, b)), VPi (t, (_, g)) ->
    ignore (extSet (infer ctx a)); eqNf (eval a ctx) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in check ctx' b (g x)
  | EPair (r, e1, e2), VSig (t, (p, g)) ->
    ignore (extSet (inferV t)); check ctx e1 t;
    check ctx e2 (g (eval e1 ctx));
    begin match p with
      | Name (v, _) -> r := Some v
      | Irrefutable -> ()
    end
  | EHole, v -> traceHole v ctx
  | e, VApp (VApp (VPathP p, u0), u1) ->
    let v0 = act e ezero ctx in
    let v1 = act e eone  ctx in
    let (i, x, v) = freshDim () in let ctx' = upLocal ctx i VI v in
    check ctx' (rbV (act e x ctx')) (appFormula p v);
    eqNf v0 u0; eqNf v1 u1
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (Ineq (VPre u, VPre v))
    | t -> raise (Ineq (VPre u, t))
  end
  | ESystem xs, VApp (VPartial t, i) ->
    eqNf (eval (getFormula xs) ctx) i;
    System.iter (fun alpha e -> check (faceEnv alpha ctx) e t) xs;

    (* check overlapping cases *)
    System.iter (fun alpha e1 ->
      System.iter (fun beta e2 ->
        if comparable alpha beta then
          let ctx' = faceEnv beta (faceEnv alpha ctx) in
          eqNf (eval e1 ctx') (eval e2 ctx')
        else ()) xs) xs
  | EInc e, VSub (t, i, u) -> check ctx e t;
    let n = freshName "υ" in
      List.iter (fun phi -> let ctx' = faceEnv phi ctx in
        eqNf (eval e ctx') (app (eval (rbV u) ctx', Var (n, isOne i)))) (solve i One)
  | e, t -> eqNf (infer ctx e) t
  with ex -> Printf.printf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e0) (showValue t0); raise ex

and infer ctx e : value = traceInfer e; match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (u + 1)
  | ESig (a, (p, b)) | EPi (a, (p, b)) -> inferTele ctx p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EApp (f, x) -> begin match infer ctx f with
    | VApp (VPartial t, i) -> check ctx x (isOne i); t
    | VPi (t, (_, g)) -> check ctx x t; g (eval x ctx)
    | v -> raise (ExpectedPi v)
  end
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (_, (_, g)) = extSigG (infer ctx e) in g (vfst (eval e ctx))
  | EField (e, p) -> inferField ctx p e
  | EPre u -> VPre (u + 1)
  | EPathP p -> inferPath ctx p
  | EPartial e -> let n = extSet (infer ctx e) in implv VI (VPre n)
  | EAppFormula (f, x) -> check ctx x VI; let (p, _, _) = extPathP (infer ctx (rbV (eval f ctx))) in
    appFormula p (eval x ctx)
  | ETransp (p, i) -> inferTransport ctx p i
  | EHComp e -> ignore (extKan (infer ctx e)); inferHComp (eval e ctx)
  | ESub (a, i, u) -> let n = extSet (infer ctx a) in check ctx i VI;
    check ctx u (VApp (VPartial (eval a ctx), eval i ctx)); VPre n
  | EI -> VPre 0 | EDir _ -> VI
  | ENeg e -> check ctx e VI; VI
  | EOr (e1, e2) | EAnd (e1, e2) -> check ctx e1 VI; check ctx e2 VI; VI
  | EId e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (implv v (VPre n))
  | ERef e -> let v = eval e ctx in let t = infer ctx e in VApp (VApp (VId t, v), v)
  | EJ e -> inferJ (eval e ctx) (infer ctx e)
  | EOuc e -> begin match infer ctx e with
    | VSub (t, _, _) -> t
    | _ -> raise (ExpectedSubtype e)
  end
  | e -> raise (InferError e)

and inferField ctx p e = match infer ctx e with
  | VSig (t, (q, _)) -> if matchIdent p q then t else inferField ctx p (ESnd e)
  | t                -> raise (ExpectedSig t)

and inferTele ctx p a b =
  ignore (extSet (infer ctx a));
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in imax (infer ctx a) v

and inferLam ctx p a e =
  ignore (extSet (infer ctx a)); let t = eval a ctx in
  ignore (infer (upLocal ctx p t (Var (p, t))) e);
  VPi (t, (p, fun x -> infer (upLocal ctx p t x) e))

and inferPath (ctx : ctx) (p : exp) =
  let (i, x, v) = freshDim () in let ctx' = upLocal ctx i VI v in
  let t = infer ctx' (rbV (act p x ctx')) in ignore (extSet t);
  let v0 = act p ezero ctx in let v1 = act p eone ctx in implv v0 (implv v1 t)

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
  implv u0 u1

and inferHComp v =
  let r = fresh (name "r") in let u = fresh (name "u") in
  VPi (VI, (r, fun r -> VPi (implv VI (VApp (VPartial v, r)), (u, fun u ->
    implv (VSub (v, r, VApp (u, VDir Zero))) v))))

and inferJ v t =
  let x = freshName "x" in let y = freshName "y" in let pi = freshName "P" in let p = freshName "p" in
  let k = extSet t in let t = VPi (v, (x, fun x -> VPi (v, (y, fun y -> implv (idv v x y) (VPre k))))) in

  VPi (t, (pi, fun pi ->
    VPi (v, (x, fun x ->
      implv (app (app (app (pi, x), x), VRef x))
            (VPi (v, (y, fun y ->
              VPi (idv v x y, (p, fun p ->
                app (app (app (pi, x), y), p))))))))))

