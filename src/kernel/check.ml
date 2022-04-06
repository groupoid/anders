open Language.Prelude
open Language.Spec
open Formula
open Trace
open Elab
open Term
open Gen
open Rbv

(* Evaluator *)
let rec eval ctx e0 = traceEval e0; match e0 with
  | EPre u               -> VPre u
  | EKan u               -> VKan u
  | EVar x               -> getRho ctx x
  | EHole                -> VHole
  | EPi  (a, (p, b))     -> let t = eval ctx a in VPi (t, (fresh p, closByVal ctx p t b))
  | ESig (a, (p, b))     -> let t = eval ctx a in VSig (t, (fresh p, closByVal ctx p t b))
  | ELam (a, (p, b))     -> let t = eval ctx a in VLam (t, (fresh p, closByVal ctx p t b))
  | EApp (f, x)          -> app (eval ctx f, eval ctx x)
  | EPair (r, e1, e2)    -> VPair (r, eval ctx e1, eval ctx e2)
  | EFst e               -> vfst (eval ctx e)
  | ESnd e               -> vsnd (eval ctx e)
  | EField (e, p)        -> evalField p (eval ctx e)
  | EId e                -> VId (eval ctx e)
  | ERef e               -> VRef (eval ctx e)
  | EJ e                 -> VJ (eval ctx e)
  | EPathP e             -> VPathP (eval ctx e)
  | EPLam e              -> VPLam (eval ctx e)
  | EAppFormula (e, x)   -> appFormula (eval ctx e) (eval ctx x)
  | EI                   -> VI
  | EDir d               -> VDir d
  | EAnd (e1, e2)        -> evalAnd (eval ctx e1) (eval ctx e2)
  | EOr (e1, e2)         -> evalOr (eval ctx e1) (eval ctx e2)
  | ENeg e               -> negFormula (eval ctx e)
  | ETransp (p, i)       -> VTransp (eval ctx p, eval ctx i)
  | EHComp (t, r, u, u0) -> hcomp (eval ctx t) (eval ctx r) (eval ctx u) (eval ctx u0)
  | EPartial e           -> let (i, _, _) = freshDim () in
    VLam (VI, (i, fun r -> let ts = mkSystem (List.map (fun mu ->
      (mu, eval (faceEnv mu ctx) e)) (solve r One)) in VPartialP (VSystem ts, r)))
  | EPartialP (t, r)     -> VPartialP (eval ctx t, eval ctx r)
  | ESystem xs           -> VSystem (evalSystem ctx xs)
  | ESub (a, i, u)       -> VSub (eval ctx a, eval ctx i, eval ctx u)
  | EInc (t, r)          -> VInc (eval ctx t, eval ctx r)
  | EOuc e               -> ouc (eval ctx e)
  | EGlue e              -> VGlue (eval ctx e)
  | EGlueElem (r, u, a)  -> glue (eval ctx r) (eval ctx u) (eval ctx a)
  | EUnglue (r, u, e)    -> unglue (eval ctx r) (eval ctx u) (eval ctx e)
  | EEmpty               -> VEmpty
  | EIndEmpty e          -> VIndEmpty (eval ctx e)
  | EUnit                -> VUnit
  | EStar                -> VStar
  | EIndUnit e           -> VIndUnit (eval ctx e)
  | EBool                -> VBool
  | EFalse               -> VFalse
  | ETrue                -> VTrue
  | EIndBool e           -> VIndBool (eval ctx e)
  | EW (a, (p, b))       -> let t = eval ctx a in W (t, (fresh p, closByVal ctx p t b))
  | ESup (a, b)          -> VSup (eval ctx a, eval ctx b)
  | EIndW (a, b, c)      -> VIndW (eval ctx a, eval ctx b, eval ctx c)
  | EIm e                -> VIm (eval ctx e)
  | EInf e               -> inf (eval ctx e)
  | EJoin e              -> join (eval ctx e)
  | EIndIm (a, b)        -> VIndIm (eval ctx a, eval ctx b)

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

and glue r u a = match r, a with
  | VDir One, _ -> vsnd (vsnd (app (u, VRef vone)))
  | _, VUnglue (_, _, b) -> b
  | _, _ -> VGlueElem (r, u, a)

and unglue r u b = match r, u, b with
  | VDir One, _, _ -> app (vfst (vsnd (app (u, VRef vone))), b)
  | _, _, VGlueElem (_, _, a) -> ouc a
  | _, _, _ -> VUnglue (r, u, b)

and transport i p phi u0 = match p, phi, u0 with
  (* transp p 1 u₀ ~> u₀ *)
  | _, VDir One, _ -> u0
  (* transp (<_> U) i A ~> A *)
  | VKan _, _, _ -> u0
  (* transp (<_> 𝟎) i u₀ ~> u₀ *)
  | VEmpty, _, _ -> u0
  (* transp (<_> 𝟏) i u₀ ~> u₀ *)
  | VUnit, _, _ -> u0
  (* transp (<_> 𝟐) i u₀ ~> u₀ *)
  | VBool, _, _ -> u0
  (* transp (<i> Π (x : A i), B i x) φ u₀ ~>
     λ (x : A 1), transp (<i> B i (transFill (<j> A -j) φ x -i)) φ
      (u₀ (transFill (<j> A -j) φ x 1)) *)
  | VPi (t, (_, b)), _, _ -> let x = fresh (ident "x") in
    let j = freshName "ι" in let k = freshName "κ" in
    VLam (act0 i vone t, (x, fun x ->
      let v = transFill j (act0 i (VNeg (dim j)) t) phi x in
      transport k (swap i k (b (v (VNeg (dim k)))))
        phi (app (u0, v vone))))
  (* transp (<i> Σ (x : A i), B i x) φ u₀ ~>
    (transp (<j> A j) φ u₀.1,
     transp (<i> B i (transFill (<j> A j) φ u₀.1 i)) φ u₀.2) *)
  | VSig (t, (_, b)), _, _ ->
    let j = freshName "ι" in let k = freshName "κ" in
    let v1 = transFill j (swap i j t) phi (vfst u0) in
    let v2 = transport k (swap i k (b (v1 (dim k)))) phi (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* transp (<i> PathP (P i) (v i) (w i)) φ u₀ ~>
     <j> comp (λ i, P i @ j) (φ ∨ j ∨ -j)
       (λ (i : I), [(φ = 1) → u₀ @ j, (j = 0) → v i, (j = 1) → w i]) (u₀ @ j) *)
  | VApp (VApp (VPathP p, v), w), _, _ ->
    let j = freshName "ι" in let k = freshName "κ" in
    VPLam (VLam (VI, (j, fun j ->
      let uj = appFormula u0 j in let r = evalOr phi (evalOr j (negFormula j)) in
      comp (fun k -> appFormula (act0 i k p) j) r k
        (VSystem (unionSystem (border (solve phi One) uj)
                 (unionSystem (border (solve j Zero) (swap i k v))
                              (border (solve j One)  (swap i k w))))) uj)))
  | VApp (VApp (VGlue a, _), VSystem u), _, _ ->
    let u' = System.map eta (forall i u) in let psi' = getFormulaV u' in

    let t1 = System.map (fun u -> transFill i (fst u) phi u0 vone) u' in
    let ts = System.map (fun u -> app (vfst (snd u), transFill i (fst u) phi u0 (dim i))) u' in

    let uj k = bimap (fun j -> if i = j then k else dim j) upd u in
    let uzero = uj vzero in let a0 = unglue (getFormulaV uzero) (VSystem uzero) u0 in

    let phi1 = solve phi One in let ksi = evalOr phi psi' in
    let a1 = comp (fun j -> act0 i j a) ksi i (VSystem (unionSystem (border phi1 a0) ts)) a0 in

    let fib = System.map (fun x -> VPair (ref None, x, idp a1))
      (unionSystem (border phi1 u0) t1) in

    let b = act0 i vone a in
    let u1 = System.map eta (uj vone) in
    let fib' = System.map (fun (t, w) ->
      (t, w, contr (fiber b t (vfst w) a1) (app (vsnd w, a1)) ksi fib)) u1 in

    let chi = getFormulaV u1 in
    let a1' = homcom b (evalOr chi phi) i
      (VSystem (unionSystem (System.map (fun (_, _, p) ->
        appFormula (vsnd p) (dim i)) fib') (border phi1 a1))) a1 in

    glue chi (VSystem (System.map (fun p -> let (t, w, u) = p in
      pairv t (pairv w (vfst u))) fib')) a1'
  (* transp (<i> W (x : A i), B i x) φ (sup (A 0) (B 0) a f) ~>
     sup (A 1) (B 1) (transp (<i> A i) φ a)
         (transp (<i> B i (transFill (<i> A i) φ a i) → (W (x : A i), B i x)) φ f) *)
  | W (t, (x, b)), _, VApp (VApp (VSup _, a), f) ->
    (* if conv (act0 i vone p) p then u0 else ??? *)
    let j = freshName "ι" in let k = freshName "κ" in let v1 = transFill j (swap i j t) phi a in
    let v2 = transport k (swap i k (implv (b (v1 (dim k))) (W (t, (x, b))))) phi f in let t' = act0 i vone t in
    VApp (VApp (VSup (t', VLam (t', (fresh x, b >> act0 i vone))), v1 vone), v2)
  (* transp (<i> ℑ (A i)) 0 (ℑ-unit a) ~> ℑ-unit (transp (<i> A i) 0 a) *)
  | VIm t, _, VInf a -> inf (transport i t phi a)
  | _, _, _ -> VApp (VTransp (VPLam (VLam (VI, (i, fun j -> act0 i j p))), phi), u0)

and transFill i p phi u0 j = let (k, _, _) = freshDim () in
  transport k (act0 i (evalAnd (dim k) j) p) (evalOr phi (negFormula j)) u0

and hcomp t r u u0 = let i = freshName "ι" in homcom t r i (app (u, dim i)) u0

and contr t p r ts = let i = freshName "ι" in let g = vsnd p in
  let ts' = System.mapi (fun mu u -> appFormula (app (upd mu g, u)) (dim i)) ts in
  homcom t r i (VSystem ts') (vfst p)

and idEquiv t =
  pairv (idfun t) (VLam (t, (freshName "x", fun x ->
    pairv (pairv x (idp x))
      (VLam (VSig (t, (freshName "y", pathv (idp t) x)),
        (freshName "u", fun u ->
          VPLam (VLam (VI, (freshName "i", fun i ->
            let p = vsnd u in pairv (appFormula p i)
              (VPLam (VLam (VI, (freshName "j", fun j ->
                appFormula p (evalAnd i j))))))))))))))

and idtoeqv i e = let a = act0 i vzero e in
  transport i (equiv a e) vzero (idEquiv a)

and walk f r = function
  | VSystem ts -> System.mapi (fun mu -> f >> upd mu) ts
  | t          -> mkSystem (List.map (fun mu ->
    (mu, upd mu (f (app (upd mu t, VRef vone))))) (solve r One))

and homcom t r i u u0 = match t, r, u, u0 with
  (* hcomp A 1 u u₀ ~> u 1 1=1 *)
  | _, VDir One, _, _ -> app (act0 i vone u, VRef vone)
  (* hcomp (Π (x : A), B x) φ u u₀ ~> λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x) *)
  | VPi (t, (x, b)), _, _, _ -> VLam (t, (fresh x, fun y -> homcom (b y) r i
    (VSystem (walk (fun v -> app (v, y)) r u)) (app (u0, y))))
   (* hcomp (Σ (x : A), B x) φ u u₀ ~>
     (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 1,
      comp (λ i, B (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 i)) φ
        (λ (k : I), [(r = 1) → (u k 1=1).2]) u₀.2) *)
  | VSig (t, (_, b)), _, _, _ -> let k = freshName "κ" in
    (* TODO: swap *)
    let v1 = hfill t r k (VSystem (walk (vfst >> act0 i (dim k)) r u)) (vfst u0) in
    let v2 = comp (v1 >> b) r i (VSystem (walk vsnd r u)) (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* hcomp (PathP A v w) φ u u₀ ~> <j> hcomp (A @ j) (λ (i : I),
      [(r = 1) → u i 1=1 @ j, (j = 0) → v, (j = 1) → w]) (u₀ @ j) *)
  | VApp (VApp (VPathP t, v), w), _, _, _ ->
    let j = freshName "ι" in
    VPLam (VLam (VI, (j, fun j ->
      homcom (appFormula t j) (evalOr r (evalOr j (negFormula j))) i
          (VSystem (unionSystem (walk (flip appFormula j) r u)
                   (unionSystem (border (solve j One)  w)
                                (border (solve j Zero) v))))
          (appFormula u0 j))))
  (* hcomp U φ E A ~> Glue A φ [(φ = 1) → (E 1 1=1, idtoeqvⁱ (E -i 1=1))] *)
  | VKan _, _, _, _ ->
    app (VApp (VGlue u0, r), VSystem (walk (fun e ->
      pairv (act0 i vone e) (idtoeqv i (act0 i (VNeg (dim i)) e))) r u))
  | VApp (VApp (VGlue a, phi), VSystem t), _, VSystem u, _ ->
    let ts = System.map (fun (t, w) -> (t, w, hfill t r i (VSystem u) u0)) (System.map eta t) in
    let t1 = System.map (fun (t, w, x) -> pairv t (pairv w (x vone))) ts in

    let a1 = homcom a (evalOr r phi) i (VSystem (unionSystem
      (System.map (fun (_, w, x) -> app (vfst w, x (dim i))) ts)
      (System.map (unglue phi (VSystem t)) u))) (unglue phi (VSystem t) u0) in
    glue phi (VSystem t1) a1
  (* hcomp (W (x : A), B x) r (λ (i : I), [(r = 1) → sup A B (a i 1=1) (f i 1=1)]) (sup A B (ouc a₀) (ouc f₀)) ~>
     sup A B (hcomp A r a (ouc a₀))
             (hcomp (B (hcomp A r a (ouc a₀)) → (W (x : A), B x)) r
                    (λ (i : I), [(r = 1) → λ (b : B (a 1 1=1)), (f i 1=1) (transp (<j> B (a (-j ∨ i) 1=1)) 0 b)])
                    (λ (b : B (hcomp A r a (ouc a₀))), (ouc f₀) (transp (<j> B (hfill A r a a₀ -j)) 0 b))) *)
  | W (t, (x, b)), _, VSystem u, VApp (VApp (VSup (_, b'), a0), f0) when System.for_all (fun _ -> isSup) u ->
    let u' = System.map extSup u in let a' = hfill t r i (VSystem (System.map fst u')) a0 in
    let a1 = a' vone in let j = freshName "ι" in let y = freshName "b" in
    let f1 = homcom (implv (b a1) (W (t, (x, b)))) r i
      (VSystem (System.map (fun (a, f) -> VLam (act0 i vone a, (y, fun y ->
          app (f, transport j (b (act0 i (evalOr (negFormula (dim j)) (dim i)) a)) vzero y)))) u'))
      (VLam (b a1, (y, fun y -> app (f0, transport j (b (a' (VNeg (dim j)))) vzero y)))) in
    VApp (VApp (VSup (t, b'), a1), f1)
  (* hcomp (ℑ A) r (λ (i : I), [(r = 1) → ℑ-unit (u i 1=1)]) (ℑ-unit (ouc u₀)) ~>
       ℑ-unit (hcomp A r u (ouc u₀)) *)
  | VIm t, _, VSystem u, VInf u0 when System.for_all (fun _ -> isInf) u ->
    VInf (homcom t r i (VSystem (System.map extInf u)) u0)
  | _, _, _, _ -> VHComp (t, r, VLam (VI, (i, fun j -> VSystem (walk (act0 i j) r u))), u0)

and comp t r i u u0 = let j = freshName "ι" in
  homcom (t vone) r i (VSystem (walk (transport j (t (evalOr (dim i) (dim j))) (dim i)) r u))
    (transport j (t (dim j)) vzero u0)

and hfill t r i u u0 j = let k = freshName "κ" in
  homcom t (evalOr (negFormula j) r) k
    (VSystem (unionSystem (walk (act0 i (evalAnd (dim k) j)) r u)
      (border (solve j Zero) u0))) u0

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
  eval (upLocal ctx' p t v) e

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
      VLam (app (b, x), (freshName "b", fun y ->
        app (VApp (VIndW (a, b, c), g), app (f, y)))))
  (* ind-ℑ A B f (ℑ-unit a) ~> f a *)
  | VApp (VIndIm _, f), VInf a -> app (f, a)
  | VApp (VIndIm (a, b), f), VHComp (_, r, u, u0) ->
    let g x = app (VApp (VIndIm (a, b), f), x) in
    let i = freshName "ι" in let k = freshName "κ" in
    comp (fun j -> VIm (app (b, hfill (VIm a) r i (app (u, dim i)) u0 j))) r k
      (VSystem (walk g r (app (u, dim k)))) (g u0)
  (* ind-ℑ A B (λ _, b) x ~> b *)
  | VApp (VIndIm (a, b), VLam (t, (x, g))), v -> let u = g (Var (x, t)) in
    if mem x u then VApp (VApp (VIndIm (a, b), VLam (t, (x, g))), v) else u
  | f, x -> VApp (f, x)

and evalSystem ctx = bimap (getRho ctx) (fun mu t -> eval (faceEnv mu ctx) t)

and getRho ctx x = match Env.find_opt x ctx with
  | Some (_, _, Value v) -> v
  | Some (_, _, Exp e)   -> eval ctx e
  | None                 -> raise (Internal (VariableNotFound x))

and appFormulaE ctx e i = eval ctx (EAppFormula (e, i))

(* This is part of evaluator, not type checker *)
and inferV v = traceInferV v; match v with
  | VPi (t, (x, f)) -> inferVTele (if !Prefs.impredicativity then impred else imax) t x f
  | VSig (t, (x, f)) | W (t, (x, f)) -> inferVTele imax t x f
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
    | v -> raise (Internal (ExpectedPi (rbV v)))
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
    | _ -> raise (Internal (ExpectedSubtype (rbV v)))
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
  | VUnglue (_, _, b) -> let (t, _, _) = extGlue (inferV b) in t
  | VEmpty | VUnit | VBool -> VKan Z.zero
  | VStar -> VUnit | VFalse | VTrue -> VBool
  | VIndEmpty t -> implv VEmpty t
  | VIndUnit t -> recUnit t
  | VIndBool t -> recBool t
  | VSup (a, b) -> inferSup a b
  | VIndW (a, b, c) -> inferIndW a b c
  | VIm t -> inferV t
  | VInf v -> VIm (inferV v)
  | VJoin v -> extIm (inferV v)
  | VIndIm (a, b) -> inferIndIm a b
  | VPLam _ | VPair _ | VHole -> raise (Internal (InferError (rbV v)))

and inferVTele g t x f = g (inferV t) (inferV (f (Var (x, t))))

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

and inferIndIm a b =
  implv (VPi (a, (freshName "a", fun x -> VIm (app (b, inf x)))))
        (VPi (VIm a, (freshName "a", fun x -> VIm (app (b, x)))))

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
  | VSystem ts           -> VSystem (bimap (actVar rho) (fun mu -> upd mu >> act rho) ts)
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
  | VGlueElem (r, u, a)  -> glue (act rho r) (act rho u) (act rho a)
  | VUnglue (r, u, b)    -> unglue (act rho r) (act rho u) (act rho b)
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
  | VIm t                -> VIm (act rho t)
  | VInf v               -> inf (act rho v)
  | VJoin v              -> join (act rho v)
  | VIndIm (a, b)        -> VIndIm (act rho a, act rho b)

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
    | VUnglue (r1, u1, b1), VUnglue (r2, u2, b2) -> conv r1 r2 && conv u1 u2 && conv b1 b2
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
    | VIm u, VIm v -> conv u v
    | VInf u, VInf v -> conv u v
    | VJoin u, VJoin v -> conv u v
    | VIndIm (a1, b1), VIndIm (a2, b2) -> conv a1 a2 && conv b1 b2
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
  with Internal _ -> false

and eqNf v1 v2 : unit = traceEqNF v1 v2;
  if conv v1 v2 then () else raise (Internal (Ineq (rbV v1, rbV v2)))

(* Type checker itself *)
and lookup ctx x = match Env.find_opt x ctx with
  | Some (_, Value v, _) -> v
  | Some (_, Exp e, _)   -> eval ctx e
  | None                 -> raise (Internal (VariableNotFound x))

and check ctx (e0 : exp) (t0 : value) =
  traceCheck e0 t0; try match e0, t0 with
  | ELam (a, (p, b)), VPi (t, (_, g)) ->
    ignore (extSet (infer ctx a)); eqNf (eval ctx a) t;
    let x = Var (p, t) in let ctx' = upLocal ctx p t x in check ctx' b (g x)
  | EPair (r, e1, e2), VSig (t, (p, g)) ->
    ignore (extSet (inferV t)); check ctx e1 t;
    check ctx e2 (g (eval ctx e1));
    begin match p with
      | Ident (v, _) -> r := Some v
      | Irrefutable -> ()
    end
  | EHole, v -> traceHole v ctx
  | EPLam (ELam (EI, (i, e))), VApp (VApp (VPathP p, u0), u1) ->
    let v = Var (i, VI) in let ctx' = upLocal ctx i VI v in
    let v0 = eval (upLocal ctx i VI vzero) e in
    let v1 = eval (upLocal ctx i VI vone) e in
    check ctx' e (appFormula p v); eqNf v0 u0; eqNf v1 u1
  | e, VPre u -> begin
    match infer ctx e with
    | VKan v | VPre v -> if ieq u v then () else raise (Internal (Ineq (EPre u, EPre v)))
    | t -> raise (Internal (Ineq (EPre u, rbV t)))
  end
  | ESystem ts, VPartialP (u, i) ->
    eqNf (eval ctx (getFormula ts)) i;
    System.iter (fun alpha e ->
      check (faceEnv alpha ctx) e
        (app (upd alpha u, VRef vone))) ts;
    checkOverlapping ctx ts
  | e, t -> eqNf (infer ctx e) t
  with exc -> let (err, es) = extTraceback (extErr exc) in raise (Internal (Traceback (err, (e0, rbV t0) :: es)))

and checkOverlapping ctx ts =
  System.iter (fun alpha e1 ->
    System.iter (fun beta e2 ->
      if comparable alpha beta then
        let ctx' = faceEnv (meet alpha beta) ctx in
        eqNf (eval ctx' e1) (eval ctx' e2)
      else ()) ts) ts

and infer ctx e : value = traceInfer e; match e with
  | EVar x -> lookup ctx x
  | EKan u -> VKan (Z.succ u)
  | EPi (a, (p, b)) -> inferTele ctx (if !Prefs.impredicativity then impred else imax) p a b
  | ESig (a, (p, b)) | EW (a, (p, b)) -> inferTele ctx imax p a b
  | ELam (a, (p, b)) -> inferLam ctx p a b
  | EPLam (ELam (EI, (i, e))) ->
    let ctx' = upLocal ctx i VI (Var (i, VI)) in ignore (infer ctx' e);
    let g = fun j -> eval (upLocal ctx i VI j) e in
    let t = VLam (VI, (freshName "ι", g >> inferV)) in
    VApp (VApp (VPathP (VPLam t), g vzero), g vone)
  | EApp (f, x) -> begin match infer ctx f with
    | VPartialP (t, i) -> check ctx x (isOne i); app (t, eval ctx x)
    | VPi (t, (_, g)) -> check ctx x t; g (eval ctx x)
    | v -> raise (Internal (ExpectedPi (rbV v)))
  end
  | EFst e -> fst (extSigG (infer ctx e))
  | ESnd e -> let (_, (_, g)) = extSigG (infer ctx e) in g (vfst (eval ctx e))
  | EField (e, p) -> inferField ctx p e
  | EPre u -> VPre (Z.succ u)
  | EPathP p -> inferPath ctx p
  | EPartial e -> let n = extSet (infer ctx e) in implv VI (VPre n)
  | EPartialP (u, r0) -> check ctx r0 VI; let t = infer ctx u in
  begin match t with
    | VPartialP (ts, r) -> eqNf r (eval ctx r0); inferV (inferV ts)
    | _ -> failwith "Expected partial function into universe"
  end
  | EAppFormula (f, x) -> check ctx x VI;
    let (p, _, _) = extPathP (infer ctx f) in
    appFormula p (eval ctx x)
  | ETransp (p, i) -> inferTransport ctx p i
  | EHComp (e, i, u, u0) -> let t = eval ctx e in let r = eval ctx i in
    ignore (extKan (infer ctx e)); check ctx i VI;
    check ctx u (implv VI (partialv t r)); check ctx u0 t;
    List.iter (fun phi -> let ctx' = faceEnv phi ctx in
      eqNf (eval ctx' (hcompval u)) (eval ctx' u0)) (solve r One); t
  | ESub (a, i, u) -> let n = extSet (infer ctx a) in check ctx i VI;
    check ctx u (partialv (eval ctx a) (eval ctx i)); VPre n
  | EI -> VPre Z.zero | EDir _ -> VI
  | ENeg e -> check ctx e VI; VI
  | EOr (e1, e2) | EAnd (e1, e2) -> check ctx e1 VI; check ctx e2 VI; VI
  | EId e -> let v = eval ctx e in let n = extSet (infer ctx e) in implv v (implv v (VPre n))
  | ERef e -> let v = eval ctx e in let t = infer ctx e in VApp (VApp (VId t, v), v)
  | EJ e -> inferJ (eval ctx e) (infer ctx e)
  | EInc (e, r) -> ignore (extKan (infer ctx e)); check ctx r VI; inferInc (eval ctx e) (eval ctx r)
  | EOuc e -> begin match infer ctx e with
    | VSub (t, _, _) -> t
    | _ -> raise (Internal (ExpectedSubtype e))
  end
  | ESystem ts -> checkOverlapping ctx ts;
    VPartialP (VSystem (System.mapi (fun mu -> infer (faceEnv mu ctx)) ts),
               eval ctx (getFormula ts))
  | EGlue e -> ignore (extKan (infer ctx e)); inferGlue (eval ctx e)
  | EGlueElem (e, u0, a) -> check ctx e VI; let r = eval ctx e in let t = infer ctx a in
    check ctx u0 (partialv (equivPtSingl t) r); let u = eval ctx u0 in
    (* Γ, φ ⊢ a ≡ f t where u = [φ ↦ (T, (f, e), t)] *)
    List.iter (fun mu -> let v = app (upd mu u, VRef vone) in let f = vfst (vfst (vsnd v)) in
      eqNf (eval (faceEnv mu ctx) a) (app (f, vsnd (vsnd v)))) (solve r One);
    inferGlueElem r u t
  | EUnglue (r, u, e) -> let (t, r', u') = extGlue (infer ctx e) in
    eqNf (eval ctx r) r'; eqNf (eval ctx u) u'; t
  | EEmpty | EUnit | EBool -> VKan Z.zero
  | EStar -> VUnit | EFalse | ETrue -> VBool
  | EIndEmpty e -> ignore (extSet (infer ctx e)); implv VEmpty (eval ctx e)
  | EIndUnit e -> inferInd false ctx VUnit e recUnit
  | EIndBool e -> inferInd false ctx VBool e recBool
  | ESup (a, b) -> let t = eval ctx a in ignore (extSet (infer ctx a));
    let (t', (p, g)) = extPiG (infer ctx b) in eqNf t t';
    ignore (extSet (g (Var (p, t))));
    inferSup t (eval ctx b)
  | EIndW (a, b, c) -> let t = eval ctx a in ignore (extSet (infer ctx a));
    let (t', (p, g)) = extPiG (infer ctx b) in
    eqNf t t'; ignore (extSet (g (Var (p, t))));

    let (w', (q, h)) = extPiG (infer ctx c) in
    eqNf (wtype t (eval ctx b)) w';
    ignore (extSet (h (Var (q, w'))));

    inferIndW t (eval ctx b) (eval ctx c)
  | EIm e -> let t = infer ctx e in ignore (extSet t); t
  | EInf e -> VIm (infer ctx e)
  | EJoin e -> let t = extIm (infer ctx e) in ignore (extIm t); t
  | EIndIm (a, b) -> ignore (extSet (infer ctx a)); let t = eval ctx a in
    let (c, (x, g)) = extPiG (infer ctx b) in eqNf (VIm t) c;
    ignore (extSet (g (Var (x, c)))); inferIndIm t (eval ctx b)
  | EPLam _ | EPair _ | EHole -> raise (Internal (InferError e))

and inferInd fibrant ctx t e f =
  let (t', (p, g)) = extPiG (infer ctx e) in eqNf t t'; let k = g (Var (p, t)) in
  ignore (if fibrant then extKan k else extSet k); f (eval ctx e)

and inferField ctx p e = snd (getField p (eval ctx e) (infer ctx e))

and inferTele ctx g p a b =
  ignore (extSet (infer ctx a));
  let t = eval ctx a in let x = Var (p, t) in
  let ctx' = upLocal ctx p t x in
  let v = infer ctx' b in g (infer ctx a) v

and inferLam ctx p a e =
  ignore (extSet (infer ctx a)); let t = eval ctx a in
  ignore (infer (upLocal ctx p t (Var (p, t))) e);
  VPi (t, (p, fun x -> inferV (eval (upLocal ctx p t x) e)))

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
    (solve (eval ctx i) One);
  implv u0 u1
