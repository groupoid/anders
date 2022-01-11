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

let reduceSystem ts x =
  match System.find_opt eps ts with
  | Some v -> v
  | None   -> VApp (VSystem ts, x)

let rec extByTag p : value -> value option = function
  | VPair (t, fst, snd) ->
  begin match !t with
    | Some q -> if p = q then Some fst else extByTag p snd
    | _      -> extByTag p snd
  end
  | _ -> None

let rec getField p v = function
  | VSig (t, (q, g)) ->
    if matchIdent p q then (vfst v, t)
    else getField p (vsnd v) (g (vfst v))
  | t -> raise (ExpectedSig t)

(* Evaluator *)
let rec eval (e0 : exp) (ctx : ctx) = traceEval e0; match e0 with
  | EPre u               -> VPre u
  | EKan u               -> VKan u
  | EVar x               -> getRho ctx x
  | EHole                -> VHole
  | EPi  (a, (p, b))     -> let t = eval a ctx in VPi (t, (fresh p, closByVal ctx p t b))
  | ESig (a, (p, b))     -> let t = eval a ctx in VSig (t, (fresh p, closByVal ctx p t b))
  | ELam (a, (p, b))     -> let t = eval a ctx in VLam (t, (fresh p, closByVal ctx p t b))
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
  | EPartial e           -> let (i, _, _) = freshDim () in
    VLam (VI, (i, fun r -> let ts = mkSystem (List.map (fun mu ->
      (mu, eval e (faceEnv mu ctx))) (solve r One)) in VPartialP (VSystem ts, r)))
  | EPartialP (t, r)     -> VPartialP (eval t ctx, eval r ctx)
  | ESystem xs           -> VSystem (evalSystem ctx xs)
  | ESub (a, i, u)       -> VSub (eval a ctx, eval i ctx, eval u ctx)
  | EInc (t, r)          -> VInc (eval t ctx, eval r ctx)
  | EOuc e               -> ouc (eval e ctx)
  | EGlue e              -> VGlue (eval e ctx)
  | EGlueElem (r, u, a)  -> VGlueElem (eval r ctx, eval u ctx, eval a ctx)
  | EUnglue e            -> VUnglue (eval e ctx)
  | EEmpty               -> VEmpty
  | EIndEmpty e          -> VIndEmpty (eval e ctx)
  | EUnit                -> VUnit
  | EStar                -> VStar
  | EIndUnit e           -> VIndUnit (eval e ctx)
  | EBool                -> VBool
  | EFalse               -> VFalse
  | ETrue                -> VTrue
  | EIndBool e           -> VIndBool (eval e ctx)
  | EW (a, (p, b))       -> let t = eval a ctx in W (t, (fresh p, closByVal ctx p t b))
  | ESup (a, b)          -> VSup (eval a ctx, eval b ctx)
  | EIndW (a, b, c)      -> VIndW (eval a ctx, eval b ctx, eval c ctx)

and appFormula v x = match v with
  | VPLam f -> app (f, x)
  | _       -> let (_, u0, u1) = extPathP (inferV v) in
    begin match x with
      | VDir Zero -> u0
      | VDir One  -> u1
      | i         -> VAppFormula (v, i)
    end

and border xs v = mkSystem (List.map (fun mu -> (mu, upd mu v)) xs)

and partialv t r = VPartialP (VSystem (border (solve r One) t) , r)

and transp p phi u0 = match p with
  | VPLam (VLam (VI, (i, g))) -> transport i (g (Var (i, VI))) phi u0
  | _ -> VApp (VTransp (p, phi), u0)

and transport i p phi u0 = match p, phi with
  (* transp p 1 u₀ ~> u₀ *)
  | _, VDir One -> u0
  (* transp (<_> U) i A ~> A *)
  | VKan _, _ -> u0
  (* transp (<_> 𝟎) i u₀ ~> u₀ *)
  | VEmpty, _ -> u0
  (* transp (<_> 𝟏) i u₀ ~> u₀ *)
  | VUnit, _ -> u0
  (* transp (<_> 𝟐) i u₀ ~> u₀ *)
  | VBool, _ -> u0
  (* transp (<i> Π (x : A i), B i x) φ u₀ ~>
     λ (x : A 1), transp (<i> B i (transFill (<j> A -j) φ x -i)) φ
      (u₀ (transFill (<j> A -j) φ x 1)) *)
  | VPi (t, (_, b)), _ -> let x = fresh (name "x") in
  let j = freshName "ι" in let k = freshName "κ" in
    VLam (act0 i vone t, (x, fun x ->
      let v = transFill j (act0 i (VNeg (dim j)) t) phi x in
      transport k (swap i k (b (v (VNeg (dim k)))))
        phi (app (u0, v vone))))
  (* transp (<i> Σ (x : A i), B i x) φ u₀ ~>
    (transp (<j> A j) φ u₀.1,
     transp (<i> B i (transFill (<j> A j) φ u₀.1 i)) φ u₀.2) *)
  | VSig (t, (_, b)), _ ->
    let j = freshName "ι" in let k = freshName "κ" in
    let v1 = transFill j (swap i j t) phi (vfst u0) in
    let v2 = transport k (swap i k (b (v1 (dim k)))) phi (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* transp (<i> PathP (P i) (v i) (w i)) φ u₀ ~>
     <j> comp (λ i, P i @ j) (φ ∨ j ∨ -j)
       (λ (i : I), [(φ = 1) → u₀ @ j, (j = 0) → v i, (j = 1) → w i]) (u₀ @ j) *)
  | VApp (VApp (VPathP p, v), w), _ ->
    let j = freshName "ι" in let k = freshName "κ" in
    VPLam (VLam (VI, (j, fun j ->
      let uj = appFormula u0 j in let r = evalOr phi (evalOr j (negFormula j)) in
      comp (fun k -> appFormula (act0 i k p) j) r k
        (VSystem (unionSystem (border (solve phi One) uj)
                 (unionSystem (border (solve j Zero) (swap i k v))
                              (border (solve j One)  (swap i k w))))) uj)))
  | _, _ -> VApp (VTransp (VPLam (VLam (VI, (i, fun j -> act0 i j p))), phi), u0)

and transFill i p phi u0 j = let (k, _, _) = freshDim () in
  transport k (act0 i (evalAnd (dim k) j) p) (evalOr phi (negFormula j)) u0

and hcomp t r u u0 = let i = freshName "ι" in kan t r i (app (u, dim i)) u0

and walk f r = function
  | VSystem ts -> System.mapi (fun mu -> f >> upd mu) ts
  | t          -> mkSystem (List.map (fun mu -> (mu,
    upd mu (f (app (upd mu t, VRef vone))))) (solve r One))

and kan t r i u u0 = match t, r with
  (* hcomp A 1 u u₀ ~> u 1 1=1 *)
  | _, VDir One -> app (act0 i vone u, VRef vone)
  (* hcomp (Π (x : A), B x) φ u u₀ ~> λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x) *)
  | VPi (t, (x, b)), _ -> VLam (t, (fresh x, fun y -> kan (b y) r i
    (VSystem (walk (fun v -> app (v, y)) r u)) (app (u0, y))))
   (* hcomp (Σ (x : A), B x) φ u u₀ ~>
     (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 1,
      comp (λ i, B (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 i)) φ
        (λ (k : I), [(r = 1) → (u k 1=1).2]) u₀.2) *)
  | VSig (t, (_, b)), _ -> let k = freshName "κ" in
    (* TODO: swap *)
    let v1 = hfill t r k (VSystem (walk (vfst >> act0 i (dim k)) r u)) (vfst u0) in
    let v2 = comp (v1 >> b) r i (VSystem (walk vsnd r u)) (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* hcomp (PathP A v w) φ u u₀ ~> <j> hcomp (A @ j) (λ (i : I),
      [(r = 1) → u i 1=1 @ j, (j = 0) → v, (j = 1) → w]) (u₀ @ j) *)
  | VApp (VApp (VPathP t, v), w), _ ->
    let j = freshName "ι" in
    VPLam (VLam (VI, (j, fun j ->
      kan (appFormula t j) (evalOr r (evalOr j (negFormula j))) i
          (VSystem (unionSystem (walk (flip appFormula j) r u)
                   (unionSystem (border (solve j One)  w)
                                (border (solve j Zero) v))))
          (appFormula u0 j))))
  | _, _ -> VHComp (t, r, VLam (VI, (i, fun j -> VSystem (walk (act0 i j) r u))), u0)

and comp t r i u u0 = let j = freshName "ι" in
  kan (t vone) r i (VSystem (walk (transport j (t (evalOr (dim i) (dim j))) (dim i)) r u))
    (transport j (t (dim j)) vzero u0)

and hfill t r i u u0 j = let k = freshName "κ" in
  kan t (evalOr (negFormula j) r) k
    (VSystem (unionSystem (walk (act0 i (evalAnd (dim k) j)) r u)
      (border (solve j Zero) u0))) u0

and inc t r = function
  | VOuc v -> v
  | v      -> VApp (VInc (t, r), v)

and ouc v = match v, inferV v with
  | _, VSub (_, VDir One, u) -> app (u, VRef vone)
  | VApp (VInc _, v), _ -> v
  | _, _ -> VOuc v

and fiber t1 t2 f y = VSig (t1, (freshName "a", fun x -> pathv (idp t2) y (app (f, x)))) (* right fiber *)

and isContr t = let x = freshName "x" in let y = freshName "y" in
  VSig (t, (x, fun x -> VPi (t, (y, fun y -> pathv (idp t) x y))))

and isEquiv t1 t2 f = VPi (t2, (freshName "b", isContr << fiber t1 t2 f))
and equiv t1 t2 = VSig (implv t1 t2, (freshName "f", isEquiv t1 t2))
and equivSingl t0 = VSig (inferV t0, (freshName "T", fun t -> equiv t t0))
and equivPtSingl t0 = VSig (inferV t0, (freshName "T", fun t -> prodv (equiv t t0) t))

and closByVal ctx p t e v = traceClos e p v;
  (* dirty hack to handle free variables introduced by type checker, for example, while checking terms like p : Path P a b *)
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval e (upLocal ctx' p t v)

and app : value * value -> value = function
  (* J A C a φ a (ref a) ~> φ *)
  | VApp (VApp (VApp (VApp (VJ _, _), _), f), _), VRef _ -> f
  (* Glue A 1 u ~> (u 1=1).1 *)
  | VApp (VGlue _, VDir One), u -> vfst (app (u, VRef vone))
  | VTransp (p, i), u0 -> transp p i u0
  | VSystem ts, x -> reduceSystem ts x
  | VLam (_, (_, f)), v -> f v
  | VInc (t, r), v -> inc t r v
  (* ind₁ C x ★ ~> x *)
  | VApp (VIndUnit _, x), VStar -> x
  (* ind₂ C a b 0₂ ~> a *)
  | VApp (VApp (VIndBool _, a), _), VFalse -> a
  (* ind₂ C a b 1₂ ~> b *)
  | VApp (VApp (VIndBool _, _), b), VTrue -> b
  (* indᵂ A B C g (sup A B x f) ~> g x f (λ (b : B x), indᵂ A B C g (f b)) *)
  | VApp (VIndW (a, b, c), g), VApp (VApp (VSup (_, _), x), f) ->
    app (app (app (g, x), f),
      VLam (app (b, x), (freshName "b", fun b ->
        app (VApp (VIndW (a, b, c), g), app (f, b)))))
  | f, x -> VApp (f, x)

and evalSystem ctx = bimap (getRho ctx) (fun beta t -> eval t (faceEnv beta ctx))

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval e ctx
  | None                 -> raise (VariableNotFound x)

and appFormulaE ctx e i = eval (EAppFormula (e, i)) ctx

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | VPi (t, (x, f)) | VSig (t, (x, f)) | W (t, (x, f)) ->
    imax (inferV t) (inferV (f (Var (x, t))))
  | VLam (t, (x, f)) -> VPi (t, (x, fun x -> inferV (f x)))
  | VPLam (VLam (VI, (_, g))) -> let t = VLam (VI, (freshName "ι", g >> inferV)) in
    VApp (VApp (VPathP (VPLam t), g vzero), g vone)
  | Var (_, t)               -> t
  | VFst e                   -> fst (extSigG (inferV e))
  | VSnd e                   -> let (_, (_, g)) = extSigG (inferV e) in g (vfst e)
  | VApp (VTransp (p, _), _) -> appFormula p vone
  | VApp (f, x)              ->
  begin match inferV f with
    | VPartialP (t, _) -> app (t, x)
    | VPi (_, (_, g)) -> g x
    | v -> raise (ExpectedPi v)
  end
  | VAppFormula (f, x)       -> let (p, _, _) = extPathP (inferV f) in appFormula p x
  | VRef v                   -> VApp (VApp (VId (inferV v), v), v)
  | VPre n                   -> VPre (Z.succ n)
  | VKan n                   -> VKan (Z.succ n)
  | VI                       -> VPre Z.zero
  | VInc (t, i)              -> inferInc t i
  | VOuc v                   ->
  begin match inferV v with
    | VSub (t, _, _) -> t
    | _ -> raise (ExpectedSubtypeV v)
  end
  | VId v -> let n = extSet (inferV v) in implv v (implv v (VPre n))
  | VJ v -> inferJ v (inferV v)
  | VPathP p -> let (_, _, v) = freshDim () in let t = inferV (appFormula p v) in
    let v0 = appFormula p vzero in let v1 = appFormula p vone in implv v0 (implv v1 t)
  | VDir _ | VOr _ | VAnd _ | VNeg _ -> VI
  | VTransp (p, _) -> implv (appFormula p vzero) (appFormula p vone)
  | VHComp (t, _, _, _) -> t
  | VSub (t, _, _) -> VPre (extSet (inferV t))
  | VPartialP (VSystem ts, _) ->
  begin match System.choose_opt ts with
    | Some (_, t) -> VPre (extSet (inferV t))
    | None        -> VPre Z.zero
  end
  | VPartialP (t, _) -> inferV (inferV t)
  | VSystem ts -> VPartialP (VSystem (System.map inferV ts), getFormulaV ts)
  | VGlue t -> inferGlue t
  | VGlueElem (r, u, a) -> inferGlueElem r u (inferV a)
  | VUnglue v -> let (t, _, _) = extGlue (inferV v) in t
  | VEmpty | VUnit | VBool -> VKan Z.zero
  | VStar -> VUnit | VFalse | VTrue -> VBool
  | VIndEmpty t -> implv VEmpty t
  | VIndUnit t -> recUnit t
  | VIndBool t -> recBool t
  | VSup (a, b) -> inferSup a b
  | VIndW (a, b, c) -> inferIndW a b c
  | VPLam _ | VPair _ | VHole -> raise (ExpectedNeutral v)

and recUnit t = let x = freshName "x" in
  implv (app (t, VStar)) (VPi (VUnit, (x, fun x -> app (t, x))))

and recBool t = let x = freshName "x" in
  implv (app (t, VFalse)) (implv (app (t, VTrue))
    (VPi (VBool, (x, fun x -> app (t, x)))))

and wtype a b = W (a, (freshName "x", fun x -> app (b, x)))

and inferSup a b = let t = wtype a b in let x = freshName "x" in
  VPi (a, (x, fun x -> implv (implv (app (b, x)) t) t))

and inferIndW a b c = let t = wtype a b in
  implv (VPi (a, (freshName "x", fun x ->
    VPi (implv (app (b, x)) t, (freshName "f", fun f ->
      implv (VPi (app (b, x), (freshName "b", fun b -> app (c, (app (f, b))))))
        (app (c, VApp (VApp (VSup (a, b), x), f))))))))
    (VPi (t, (freshName "w", fun w -> app (c, w))))

and inferInc t r = let a = freshName "a" in
  VPi (t, (a, fun v -> VSub (t, r, VSystem (border (solve r One) v))))

and inferGlue t = let (r, _, _) = freshDim () in let k = inferV t in
  VPi (VI, (r, fun r -> implv (partialv (equivSingl t) r) k))

and inferGlueElem r u t =
  VApp (VApp (VGlue t, r), VSystem (walk (fun v -> VPair (ref None, vfst v, vfst (vsnd v))) r u))

and inferJ v t =
  let x = freshName "x" in let y = freshName "y" in let pi = freshName "P" in let p = freshName "p" in
  let k = extSet t in let t = VPi (v, (x, fun x -> VPi (v, (y, fun y -> implv (idv v x y) (VPre k))))) in

  VPi (t, (pi, fun pi ->
    VPi (v, (x, fun x ->
      implv (app (app (app (pi, x), x), VRef x))
            (VPi (v, (y, fun y ->
              VPi (idv v x y, (p, fun p ->
                app (app (app (pi, x), y), p))))))))))

and evalField p v = match extByTag p v with
  | None   -> fst (getField p v (inferV v))
  | Some k -> k

and updTerm alpha = function
  | Exp e   -> Exp e
  | Value v -> Value (upd alpha v)

and faceEnv alpha ctx =
  Env.map (fun (p, t, v) -> if p = Local then (p, updTerm alpha t, updTerm alpha v) else (p, t, v)) ctx
  |> Env.fold (fun p dir -> Env.add p (Local, Value VI, Value (VDir dir))) alpha

and act rho = function
  | VLam (t, (x, g))     -> VLam (act rho t, (x, g >> act rho))
  | VPair (r, u, v)      -> VPair (r, act rho u, act rho v)
  | VKan u               -> VKan u
  | VPi (t, (x, g))      -> VPi (act rho t, (x, g >> act rho))
  | VSig (t, (x, g))     -> VSig (act rho t, (x, g >> act rho))
  | VPre u               -> VPre u
  | VPLam f              -> VPLam (act rho f)
  | Var (i, VI)          -> actVar rho i
  | Var (x, t)           -> Var (x, act rho t)
  | VApp (f, x)          -> app (act rho f, act rho x)
  | VFst k               -> vfst (act rho k)
  | VSnd k               -> vsnd (act rho k)
  | VHole                -> VHole
  | VPathP v             -> VPathP (act rho v)
  | VPartialP (t, r)     -> VPartialP (act rho t, act rho r)
  | VSystem ts           -> VSystem (bimap (actVar rho) (fun beta -> upd beta >> act rho) ts)
  | VSub (t, i, u)       -> VSub (act rho t, act rho i, act rho u)
  | VTransp (p, i)       -> VTransp (act rho p, act rho i)
  | VHComp (t, r, u, u0) -> hcomp (act rho t) (act rho r) (act rho u) (act rho u0)
  | VAppFormula (f, x)   -> appFormula (act rho f) (act rho x)
  | VId v                -> VId (act rho v)
  | VRef v               -> VRef (act rho v)
  | VJ v                 -> VJ (act rho v)
  | VI                   -> VI
  | VDir d               -> VDir d
  | VAnd (u, v)          -> evalAnd (act rho u) (act rho v)
  | VOr (u, v)           -> evalOr (act rho u) (act rho v)
  | VNeg u               -> negFormula (act rho u)
  | VInc (t, r)          -> VInc (act rho t, act rho r)
  | VOuc v               -> ouc (act rho v)
  | VGlue v              -> VGlue (act rho v)
  | VGlueElem (r, u, a)  -> VGlueElem (act rho r, act rho u, act rho a)
  | VUnglue v            -> VUnglue (act rho v)
  | VEmpty               -> VEmpty
  | VIndEmpty v          -> VIndEmpty (act rho v)
  | VUnit                -> VUnit
  | VStar                -> VStar
  | VIndUnit v           -> VIndUnit (act rho v)
  | VBool                -> VBool
  | VFalse               -> VFalse
  | VTrue                -> VTrue
  | VIndBool v           -> VIndBool (act rho v)
  | W (t, (x, g))        -> W (act rho t, (x, g >> act rho))
  | VSup (a, b)          -> VSup (act rho a, act rho b)
  | VIndW (a, b, c)      -> VIndW (act rho a, act rho b, act rho c)

and actVar rho i = match Env.find_opt i rho with
  | Some v -> v
  | None   -> Var (i, VI)

and act0 i j = act (Env.add i j Env.empty)

and upd mu = act (Env.map dir mu)

(* Convertibility *)
and conv v1 v2 : bool = traceConv v1 v2;
  v1 == v2 || begin match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (_, a, b), VPair (_, c, d) -> conv a c && conv b d
    | VPair (_, a, b), v | v, VPair (_, a, b) -> conv (vfst v) a && conv (vsnd v) b
    | VPi  (a, (p, f)), VPi  (b, (_, g))
    | VSig (a, (p, f)), VSig (b, (_, g))
    | VLam (a, (p, f)), VLam (b, (_, g))
    | W    (a, (p, f)), W    (b, (_, g)) ->
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
    | VPartialP (t1, r1), VPartialP (t2, r2) -> conv t1 t2 && conv r1 r2
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
    | VGlue v, VGlue u -> conv u v
    | VGlueElem (r1, u1, a1), VGlueElem (r2, u2, a2) -> conv r1 r2 && conv u1 u2 && conv a1 a2
    | VUnglue v, VUnglue u -> conv u v
    | VEmpty, VEmpty -> true
    | VIndEmpty u, VIndEmpty v -> conv u v
    | VUnit, VUnit -> true
    | VStar, VStar -> true
    | VIndUnit u, VIndUnit v -> conv u v
    | VBool, VBool -> true
    | VFalse, VFalse -> true
    | VTrue, VTrue -> true
    | VIndBool u, VIndBool v -> conv u v
    | VSup (a1, b1), VSup (a2, b2) -> conv a1 a2 && conv b1 b2
    | VIndW (a1, b1, c1), VIndW (a2, b2, c2) -> conv a1 a2 && conv b1 b2 && conv c1 c2
    | _, _ -> false
  end || convWithSystem (v1, v2) || convProofIrrel v1 v2

and convWithSystem = function
  | v, VApp (VSystem ts, _) | VApp (VSystem ts, _), v ->
    System.for_all (fun mu -> conv (upd mu v)) ts
  | _, _ -> false

and convProofIrrel v1 v2 =
  try match inferV v1, inferV v2 with
    (* Id A a b is proof-irrelevant *)
    | VApp (VApp (VId t1, a1), b1), VApp (VApp (VId t2, a2), b2) -> conv t1 t2 && conv a1 a2 && conv b1 b2
    | VEmpty, VEmpty -> !Prefs.irrelevance
    | VUnit, VUnit -> !Prefs.irrelevance
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
  | EPLam (ELam (EI, (i, e))), VApp (VApp (VPathP p, u0), u1) ->
    let v = Var (i, VI) in let ctx' = upLocal ctx i VI v in
    let v0 = eval e (upLocal ctx i VI vzero) in
    let v1 = eval e (upLocal ctx i VI vone) in
    check ctx' e (appFormula p v); eqNf v0 u0; eqNf v1 u1
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (Ineq (VPre u, VPre v))
    | t -> raise (Ineq (VPre u, t))
  end
  | ESystem ts, VPartialP (u, i) ->
    eqNf (eval (getFormula ts) ctx) i;
    System.iter (fun alpha e ->
      check (faceEnv alpha ctx) e
        (app (upd alpha u, VRef vone))) ts;
    checkOverlapping ctx ts
  | e, t -> eqNf (infer ctx e) t
  with ex -> Printf.printf "When trying to typecheck\n  %s\nAgainst type\n  %s\n" (showExp e0) (showValue t0); raise ex

and checkOverlapping ctx ts =
  System.iter (fun alpha e1 ->
    System.iter (fun beta e2 ->
      if comparable alpha beta then
        let ctx' = faceEnv (meet alpha beta) ctx in
        eqNf (eval e1 ctx') (eval e2 ctx')
      else ()) ts) ts

and infer ctx e : value = traceInfer e; match e with
  | EVar x -> lookup x ctx
  | EKan u -> VKan (Z.succ u)
  | ESig (a, (p, b)) | EPi (a, (p, b)) | EW (a, (p, b)) -> inferTele ctx p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EPLam (ELam (EI, (i, e))) ->
    let ctx' = upLocal ctx i VI (Var (i, VI)) in ignore (infer ctx' e);
    let g = fun j -> eval e (upLocal ctx i VI j) in
    let t = VLam (VI, (freshName "ι", g >> inferV)) in
    VApp (VApp (VPathP (VPLam t), g vzero), g vone)
  | EApp (f, x) -> begin match infer ctx f with
    | VPartialP (t, i) -> check ctx x (isOne i); app (t, eval x ctx)
    | VPi (t, (_, g)) -> check ctx x t; g (eval x ctx)
    | v -> raise (ExpectedPi v)
  end
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (_, (_, g)) = extSigG (infer ctx e) in g (vfst (eval e ctx))
  | EField (e, p) -> inferField ctx p e
  | EPre u -> VPre (Z.succ u)
  | EPathP p -> inferPath ctx p
  | EPartial e -> let n = extSet (infer ctx e) in implv VI (VPre n)
  | EPartialP (u, r0) -> check ctx r0 VI; let t = infer ctx u in
  begin match t with
    | VPartialP (ts, r) -> eqNf r (eval r0 ctx); inferV (inferV ts)
    | _ -> failwith "Expected partial function into universe"
  end
  | EAppFormula (f, x) -> check ctx x VI;
    let (p, _, _) = extPathP (infer ctx f) in
    appFormula p (eval x ctx)
  | ETransp (p, i) -> inferTransport ctx p i
  | EHComp (e, i, u, u0) -> let t = eval e ctx in let r = eval i ctx in
    ignore (extKan (infer ctx e)); check ctx i VI;
    check ctx u (implv VI (partialv t r)); check ctx u0 t;
    List.iter (fun phi -> let ctx' = faceEnv phi ctx in
      eqNf (eval (hcompval u) ctx') (eval u0 ctx')) (solve r One); t
  | ESub (a, i, u) -> let n = extSet (infer ctx a) in check ctx i VI;
    check ctx u (partialv (eval a ctx) (eval i ctx)); VPre n
  | EI -> VPre Z.zero | EDir _ -> VI
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
  | ESystem ts -> checkOverlapping ctx ts;
    VPartialP (VSystem (System.mapi (fun mu -> infer (faceEnv mu ctx)) ts),
               eval (getFormula ts) ctx)
  | EGlue e -> ignore (extKan (infer ctx e)); inferGlue (eval e ctx)
  | EGlueElem (e, u0, a) -> check ctx e VI; let r = eval e ctx in let t = infer ctx a in
    check ctx u0 (partialv (equivPtSingl t) r); let u = eval u0 ctx in
    (* Γ, φ ⊢ a ≡ f t where u = [φ ↦ (T, (f, e), t)] *)
    List.iter (fun mu -> let v = app (upd mu u, VRef vone) in let f = vfst (vfst (vsnd v)) in
      eqNf (eval a (faceEnv mu ctx)) (app (f, vsnd (vsnd v)))) (solve r One);
    inferGlueElem r u t
  | EUnglue e -> let (t, _, _) = extGlue (infer ctx e) in t
  | EEmpty | EUnit | EBool -> VKan Z.zero
  | EStar -> VUnit | EFalse | ETrue -> VBool
  | EIndEmpty e -> ignore (extSet (infer ctx e)); implv VEmpty (eval e ctx)
  | EIndUnit e -> inferInd false ctx VUnit e recUnit
  | EIndBool e -> inferInd false ctx VBool e recBool
  | ESup (a, b) -> let t = eval a ctx in ignore (extSet (infer ctx a));
    let (t', (p, g)) = extPiG (infer ctx b) in eqNf t t';
    ignore (extSet (g (Var (p, t))));
    inferSup t (eval b ctx)
  | EIndW (a, b, c) -> let t = eval a ctx in ignore (extSet (infer ctx a));
    let (t', (p, g)) = extPiG (infer ctx b) in
    eqNf t t'; ignore (extSet (g (Var (p, t))));

    let (w', (q, h)) = extPiG (infer ctx c) in
    eqNf (wtype t (eval b ctx)) w';
    ignore (extSet (h (Var (q, w'))));

    inferIndW t (eval b ctx) (eval c ctx)
  | EPLam _ | EPair _ | EHole -> raise (InferError e)

and inferInd fibrant ctx t e f =
  let (t', (p, g)) = extPiG (infer ctx e) in eqNf t t'; let k = g (Var (p, t)) in
  ignore (if fibrant then extKan k else extSet k); f (eval e ctx)

and inferField ctx p e = snd (getField p (eval e ctx) (infer ctx e))

and inferTele ctx p a b =
  ignore (extSet (infer ctx a));
  let t = eval a ctx in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in imax (infer ctx a) v

and inferLam ctx p a e =
  ignore (extSet (infer ctx a)); let t = eval a ctx in
  ignore (infer (upLocal ctx p t (Var (p, t))) e);
  VPi (t, (p, fun x -> inferV (eval e (upLocal ctx p t x))))

and inferPath ctx p =
  let (_, t0, t1) = extPathP (infer ctx p) in
  (* path cannot connect different universes,
     so if one endpoint is in U, then so other *)
  let k = extSet (inferV t0) in implv t0 (implv t1 (VKan k))

and inferTransport ctx p i =
  check ctx i VI;
  let u0 = appFormulaE ctx p ezero in
  let u1 = appFormulaE ctx p eone in

  let (t, _, _) = extPathP (infer ctx p) in
  ignore (extKan (inferV (appFormula t (Var (freshName "ι", VI)))));

  let (j, e, v) = freshDim () in let ctx' = upLocal ctx j VI v in

  (* Check that p is constant at i = 1 *)
  List.iter (fun phi -> let rho = faceEnv phi ctx' in
    eqNf (appFormulaE rho p ezero) (appFormulaE rho p e))
    (solve (eval i ctx) One);
  implv u0 u1