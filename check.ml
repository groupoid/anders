open Prettyprinter
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
  | EPre u               -> VPre u
  | EKan u               -> VKan u
  | EVar x               -> getRho ctx x
  | EHole                -> VHole
  | EPi  (a, (p, b))     -> let t = eval a ctx in VPi (t, (p, closByVal ctx p t b))
  | ESig (a, (p, b))     -> let t = eval a ctx in VSig (t, (p, closByVal ctx p t b))
  | ELam (a, (p, b))     -> let t = eval a ctx in VLam (t, (p, closByVal ctx p t b))
  | EApp (f, x)          -> app (eval f ctx, eval x ctx)
  | EPair (r, e1, e2)    -> VPair (r, eval e1 ctx, eval e2 ctx)
  | EFst e               -> vfst (eval e ctx)
  | ESnd e               -> vsnd (eval e ctx)
  | EField (e, p)        -> evalField p (eval e ctx)
  | EId e                -> VId (eval e ctx)
  | ERef e               -> VRef (eval e ctx)
  | EJ e                 -> VJ (eval e ctx)
  | EPathP e             -> VPathP (eval e ctx)
  | EPLam e              -> VPLam (eval e ctx)
  | EAppFormula (e, x)   -> appFormula (eval e ctx) (eval x ctx)
  | EI                   -> VI
  | EDir d               -> VDir d
  | EAnd (e1, e2)        -> evalAnd (eval e1 ctx) (eval e2 ctx)
  | EOr (e1, e2)         -> evalOr (eval e1 ctx) (eval e2 ctx)
  | ENeg e               -> negFormula (eval e ctx)
  | ETransp (p, i)       -> VTransp (eval p ctx, eval i ctx)
  | EHComp (t, r, u, u0) -> hcomp (eval t ctx) (eval r ctx) (eval u ctx) (eval u0 ctx)
  | EPartial e           -> VPartial (eval e ctx)
  | ESystem xs           -> VSystem (evalSystem ctx xs)
  | ESub (a, i, u)       -> VSub (eval a ctx, eval i ctx, eval u ctx)
  | EInc (t, r)          -> VInc (eval t ctx, eval r ctx)
  | EOuc e               -> evalOuc (eval e ctx)

and appFormula v x = match v with
  | VPLam f -> app (f, x)
  | _       -> let (_, u0, u1) = extPathP (inferV v) in
    begin match x with
      | VDir Zero -> u0
      | VDir One  -> u1
      | i         -> VAppFormula (v, i)
    end

and border xs v = mkSystem (List.map (fun alpha -> (alpha, upd alpha v)) xs)

and transport p phi u0 = let (_, _, v) = freshDim () in match appFormula p v, phi with
  (* transp p 1 u₀ ~> u₀ *)
  | _, VDir One -> u0
  (* transp (<_> U) i A ~> A *)
  | VKan _, _ -> u0
  (* transp (<i> Π (x : A i), B i x) φ u₀ ~>
     λ (x : A 1), transp (<i> B i (transFill (<j> A -j) φ x i)) φ
      (u₀ (transFill (<j> A -j) φ x 1)) *)
  | VPi _, _ -> let x = fresh (name "x") in
    let (i, _, _) = freshDim () in let (j, _, _) = freshDim () in
    let (t, _) = extPiG (appFormula p vone) in
    VLam (t, (x, fun x ->
      let v = transFill (VPLam (VLam (VI, (j, fun j ->
        fst (extPiG (appFormula p (negFormula j))))))) phi x in
      transport (VPLam (VLam (VI, (i, fun i ->
        let (_, (_, b)) = extPiG (appFormula p i) in
          b (v (negFormula i))))))
        phi (app (u0, v vone))))
  (* transp (<i> Σ (x : A i), B i x) φ u₀ ~>
    (transp (<j> A j) φ u₀.1,
     transp (<i> B i (transFill (<j> A j) φ u₀.1 i)) φ u₀.2) *)
  | VSig _, _ ->
    let (i, _, _) = freshDim () in let (j, _, _) = freshDim () in
    let a = VPLam (VLam (VI, (j, fun j -> fst (extSigG (appFormula p j))))) in
    let v1 = transFill a phi (vfst u0) in
    let v2 = transport (VPLam (VLam (VI, (i, fun i ->
      let (_, (_, b)) = extSigG (appFormula p i) in
        b (v1 i))))) phi (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* transp (<i> PathP (P i) (v i) (w i)) φ u₀ ~>
     <j> comp (λ i, P i @ j) (φ ∨ j ∨ -j)
       (λ (i : I), [(φ = 1) → u₀ @ j, (j = 0) → v i, (j = 1) → w i]) (u₀ @ j) *)
  | VApp (VApp (VPathP _, _), _), _ ->
    let i = fresh (name "ι") in let j = fresh (name "υ") in
    VPLam (VLam (VI, (j, fun j ->
      let uj = appFormula u0 j in let r = orFormula (phi, orFormula (j, negFormula j)) in
      comp (fun i -> let (q, _, _) = extPathP (appFormula p i) in appFormula q j) r
        (VLam (VI, (i, fun i ->
          let (_, v, w) = extPathP (appFormula p i) in
          VSystem (unionSystem (border (solve phi One) uj)
                    (unionSystem (border (solve j Zero) v)
                                 (border (solve j One) w)))))) uj)))
  | _, _ -> VApp (VTransp (p, phi), u0)

and hcomp t r u u0 = match t, r with
  | _, VDir One -> app (app (u, vone), VRef vone)
  (* hcomp (Π (x : A), B x) φ u u₀ ~> λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x) *)
  | VPi (t, (_, b)), _ -> let (i, _, _) = freshDim () in let x = fresh (name "x") in
    VLam (t, (x, fun x ->
      hcomp (b x) r (VLam (VI, (i, fun i ->
        VSystem (border (solve r One)
          (app (app (app (u, i), VRef vone), x)))))) (app (u0, x))))
   (* hcomp (Σ (x : A), B x) φ u u₀ ~>
     (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 1,
      comp (λ i, B (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 i)) φ
        (λ (k : I), [(r = 1) → (u k 1=1).2]) u₀.2) *)
  | VSig (t, (_, b)), _ ->
    let (k, _, _) = freshDim () in
    let v1 = hfill t r (VLam (VI, (k, fun k ->
      VSystem (border (solve r One)
        (vfst (app (app (u, k), VRef vone))))))) (vfst u0) in
    let v2 = comp (v1 >> b) r (VLam (VI, (k, fun k ->
      VSystem (border (solve r One)
        (vsnd (app (app (u, k), VRef vone))))))) (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* hcomp (PathP A v w) φ u u₀ ~> <j> hcomp (A @ j) (λ (i : I),
      [(r = 1) → u i 1=1, (j = 0) → v, (j = 1) → w]) (u₀ @ j) *)
  | VApp (VApp (VPathP t, v), w), _ ->
    let (j, _, _) = freshDim () in let (i, _, _) = freshDim () in
    VPLam (VLam (VI, (j, fun j ->
      hcomp (appFormula t j) (orFormula (r, orFormula (j, negFormula j)))
        (VLam (VI, (i, fun i ->
          (VSystem (unionSystem (border (solve r One) (appFormula (app (app (u, i), VRef vone)) j))
            (unionSystem (border (solve j Zero) v) (border (solve j One) w)))))))
          (appFormula u0 j))))
  | _, _ -> VHComp (t, r, u, u0)

and inc t r v = app (VInc (t, r), v)

and comp t r u u0 =
  let (i, _, _) = freshDim () in let (j, _, _) = freshDim () in
  hcomp (t vone) r (VLam (VI, (i, fun i ->
    let u1 = transport (VPLam (VLam (VI, (j, fun j -> t (orFormula (i, j)))))) i (app (app (u, i), VRef vone)) in
      VSystem (border (solve r One) u1))))
    (transport (VPLam (VLam (VI, (i, t)))) vzero u0)

and hfill t r u u0 j =
  let (i, _, _) = freshDim () in
  hcomp t (orFormula (negFormula j, r))
    (VLam (VI, (i, fun i ->
      VSystem (unionSystem (border (solve r One)
        (app (app (u, andFormula (i, j)), VRef vone)))
          (border (solve j Zero) u0))))) u0

and transFill p phi u0 j = let (i, _, _) = freshDim () in
  transport (VPLam (VLam (VI, (i, fun i -> appFormula p (andFormula (i, j))))))
    (orFormula (phi, negFormula j)) u0

and closByVal ctx p t e v = traceClos e p v;
  (* dirty hack to handle free variables introduced by type checker,
     for example, while checking terms like p : Path P a b *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and app : value * value -> value = function
  | VApp (VApp (VApp (VApp (VJ _, _), _), f), _), VRef _ -> f
  | VTransp (p, i), u0 -> transport p i u0
  | VSystem ts, x -> reduceSystem ts x
  | VLam (_, (_, f)), v -> f v
  | VInc _, VOuc v -> v
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
    not (List.exists (fun (beta, _) -> lt beta alpha) ts')) ts'
  |> mkSystem

and reduceSystem ts x =
  match System.find_opt eps ts with
  | Some v -> v
  | None   -> VApp (VSystem ts, x)

and evalOuc v = match v, inferV v with
  | _, VSub (_, VDir One, u) -> app (u, VRef vone)
  | VApp (VInc _, v), _ -> v
  | _, _ -> VOuc v

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
  | VInc (t, i)              -> inferInc t i
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
  | VHComp (t, _, _, _) -> t
  | VSub (a, _, _) -> VPre (extSet (inferV a))
  | VPartial v -> let n = extSet (inferV v) in implv VI (VPre n)
  | v -> raise (ExpectedNeutral v)

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
  | VLam (t, (x, g))     -> VLam (upd e t, (x, g >> upd e))
  | VPair (r, u, v)      -> VPair (r, upd e u, upd e v)
  | VKan u               -> VKan u
  | VPi (t, (x, g))      -> VPi (upd e t, (x, g >> upd e))
  | VSig (t, (x, g))     -> VSig (upd e t, (x, g >> upd e))
  | VPre u               -> VPre u
  | VPLam f              -> VPLam (upd e f)
  | Var (i, VI)          ->
    begin match Env.find_opt i e with
      | Some d -> VDir d
      | None   -> Var (i, VI)
    end
  | Var (x, t)           -> Var (x, upd e t)
  | VApp (f, x)          -> app (upd e f, upd e x)
  | VFst k               -> vfst (upd e k)
  | VSnd k               -> vsnd (upd e k)
  | VHole                -> VHole
  | VPathP v             -> VPathP (upd e v)
  | VPartial v           -> VPartial (upd e v)
  | VSystem ts           ->
    VSystem (System.bindings ts
            |> List.filter_map (fun (e', v) ->
              if compatible e e' then
                Some (Env.filter (fun k _ -> not (Env.mem k e)) e', upd e v)
              else None)
            |> mkSystem)
  | VSub (t, i, u)       -> VSub (upd e t, upd e i, upd e u)
  | VTransp (p, i)       -> VTransp (upd e p, upd e i)
  | VHComp (t, r, u, u0) -> hcomp (upd e t) (upd e r) (upd e u) (upd e u0)
  | VAppFormula (f, x)   -> appFormula (upd e f) (upd e x)
  | VId v                -> VId (upd e v)
  | VRef v               -> VRef (upd e v)
  | VJ v                 -> VJ (upd e v)
  | VI                   -> VI
  | VDir d               -> VDir d
  | VAnd (u, v)          -> andFormula (upd e u, upd e v)
  | VOr (u, v)           -> orFormula (upd e u, upd e v)
  | VNeg u               -> negFormula (upd e u)
  | VInc (t, r)          -> VInc (upd e t, upd e r)
  | VOuc v               -> evalOuc (upd e v)

and updTerm alpha = function
  | Exp e   -> Exp e
  | Value v -> Value (upd alpha v)

and faceEnv alpha ctx =
  Env.map (fun (p, t, v) -> if p = Local then (p, updTerm alpha t, updTerm alpha v) else (p, t, v)) ctx
  |> Env.fold (fun p dir -> Env.add p (Local, Value VI, Value (VDir dir))) alpha

(* Readback *)
and rbV v : exp = traceRbV v; match v with
  | VLam (t, g)          -> rbVTele eLam t g
  | VPair (r, u, v)      -> EPair (r, rbV u, rbV v)
  | VKan u               -> EKan u
  | VPi (t, g)           -> rbVTele ePi t g
  | VSig (t, g)          -> rbVTele eSig t g
  | VPre u               -> EPre u
  | VPLam f              -> EPLam (rbV f)
  | Var (x, _)           -> EVar x
  | VApp (f, x)          -> EApp (rbV f, rbV x)
  | VFst k               -> EFst (rbV k)
  | VSnd k               -> ESnd (rbV k)
  | VHole                -> EHole
  | VPathP v             -> EPathP (rbV v)
  | VPartial v           -> EPartial (rbV v)
  | VSystem ts           -> ESystem (System.map rbV ts)
  | VSub (a, i, u)       -> ESub (rbV a, rbV i, rbV u)
  | VTransp (p, i)       -> ETransp (rbV p, rbV i)
  | VHComp (t, r, u, u0) -> EHComp (rbV t, rbV r, rbV u, rbV u0)
  | VAppFormula (f, x)   -> EAppFormula (rbV f, rbV x)
  | VId v                -> EId (rbV v)
  | VRef v               -> ERef (rbV v)
  | VJ v                 -> EJ (rbV v)
  | VI                   -> EI
  | VDir d               -> EDir d
  | VAnd (u, v)          -> EAnd (rbV u, rbV v)
  | VOr (u, v)           -> EOr (rbV u, rbV v)
  | VNeg u               -> ENeg (rbV u)
  | VInc (t, r)          -> EInc (rbV t, rbV r)
  | VOuc v               -> EOuc (rbV v)

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
    | VSystem xs, x | x, VSystem xs -> System.for_all (fun alpha y -> conv (app (upd alpha x, VRef vone)) y) xs
    | VTransp (p, i), VTransp (q, j) -> conv p q && conv i j
    | VHComp (t1, r1, u1, v1), VHComp (t2, r2, u2, v2) -> conv t1 t2 && conv r1 r2 && conv u1 u2 && conv v1 v2
    | VSub (a, i, u), VSub (b, j, v) -> conv a b && conv i j && conv u v
    | VOr (x, y), VDir Zero | VAnd (x, y), VDir One  -> conv x v2 && conv y v2
    | VOr (x, y), VDir One  | VAnd (x, y), VDir Zero -> conv x v2 || conv y v2
    | VOr _,  _ | _, VOr _  -> orEq v1 v2
    | VAnd _, _ | _, VAnd _ -> andEq v1 v2
    | VNeg x, VNeg y -> conv x y
    | VI, VI -> true
    | VDir u, VDir v -> u = v
    | VId u, VId v | VJ u, VJ v -> conv u v
    | VInc (t1, r1), VInc (t2, r2) -> conv t1 t2 && conv r1 r2
    | VOuc u, VOuc v -> conv u v
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
    System.iter (fun alpha e -> check (faceEnv alpha ctx) e (upd alpha t)) xs;

    (* check overlapping cases *)
    System.iter (fun alpha e1 ->
      System.iter (fun beta e2 ->
        if comparable alpha beta then
          let ctx' = faceEnv (meet alpha beta) ctx in
          eqNf (eval e1 ctx') (eval e2 ctx')
        else ()) xs) xs
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
  | EHComp (e, i, u, u0) -> let t = eval e ctx in let r = eval i ctx in
    ignore (extKan (infer ctx e)); check ctx i VI;
    check ctx u (implv VI (partialv t r)); check ctx u0 t;
    List.iter (fun phi -> let ctx' = faceEnv phi ctx in
      eqNf (eval (hcompval u) ctx') (eval u0 ctx')) (solve r One); t
  | ESub (a, i, u) -> let n = extSet (infer ctx a) in check ctx i VI;
    check ctx u (partialv (eval a ctx) (eval i ctx)); VPre n
  | EI -> VPre 0 | EDir _ -> VI
  | ENeg e -> check ctx e VI; VI
  | EOr (e1, e2) | EAnd (e1, e2) -> check ctx e1 VI; check ctx e2 VI; VI
  | EId e -> let v = eval e ctx in let n = extSet (infer ctx e) in implv v (implv v (VPre n))
  | ERef e -> let v = eval e ctx in let t = infer ctx e in VApp (VApp (VId t, v), v)
  | EJ e -> inferJ (eval e ctx) (infer ctx e)
  | EInc (e, r) -> ignore (extKan (infer ctx e)); check ctx r VI; inferInc (eval e ctx) (eval r ctx)
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
  VPi (t, (p, fun x -> inferV (eval e (upLocal ctx p t x))))

and inferPath (ctx : ctx) (p : exp) =
  let (i, x, v) = freshDim () in let ctx' = upLocal ctx i VI v in
  let t = infer ctx' (rbV (act p x ctx')) in ignore (extSet t);
  let v0 = act p ezero ctx in let v1 = act p eone ctx in implv v0 (implv v1 t)

and inferInc t r = let a = freshName "a" in
  VPi (t, (a, fun v -> VSub (t, r, VSystem (border (solve r One) v))))

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

and inferJ v t =
  let x = freshName "x" in let y = freshName "y" in let pi = freshName "P" in let p = freshName "p" in
  let k = extSet t in let t = VPi (v, (x, fun x -> VPi (v, (y, fun y -> implv (idv v x y) (VPre k))))) in

  VPi (t, (pi, fun pi ->
    VPi (v, (x, fun x ->
      implv (app (app (app (pi, x), x), VRef x))
            (VPi (v, (y, fun y ->
              VPi (idv v x y, (p, fun p ->
                app (app (app (pi, x), y), p))))))))))

