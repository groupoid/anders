open Language.Prelude
open Language.Spec
open Formula
open Trace
open Elab
open Term
open Gen
open Rbv

let timeout = 1000.0
let startTime = ref (Unix.gettimeofday ())
let fuel = ref 1000000
let conv_depth = ref 0
let reset_conv_depth () = conv_depth := 0

let conv_cache_size = 1048576
let conv_cache = Array.make conv_cache_size (VHole, VHole, false)
let conv_cache_idx = ref 0

let act_cache_size = 1048576
let act_cache = Array.make act_cache_size (Env.empty, VHole, VHole)
let act_cache_idx = ref 0

let app_cache_size = 1048576
let app_cache = Array.make app_cache_size (VHole, VHole, VHole)

let transport_cache_size = 1048576
let transport_cache = Array.make transport_cache_size (Ident ("", 0L), VHole, VHole, VHole, VHole)
let app_hits = ref 0
let app_misses = ref 0
let trans_hits = ref 0
let trans_misses = ref 0
let conv_hits = ref 0
let conv_misses = ref 0

let print_stats () =
  if !Prefs.trace then
    Printf.printf "App Cache: %d hits, %d misses | Trans Cache: %d hits, %d misses | Conv Cache: %d hits, %d misses\n%!"
      !app_hits !app_misses !trans_hits !trans_misses !conv_hits !conv_misses

let burn () =
  fuel := !fuel - 1;
  if !fuel <= 0 then (
    fuel := 1000000;
    print_stats ();
    if Unix.gettimeofday () -. !startTime > timeout then failwith "Termination limit reached"
  )
let reset_fuel () = startTime := Unix.gettimeofday (); fuel := 1000000

let mem i v = IdentSet.mem i (get_support v)

let is_constant_clos (p, f) =
  let v = f (Var (p, VI)) in
  not (IdentSet.mem p (get_support v))

let is_constant_motive = function
  | VLam (_, clos) -> is_constant_clos clos
  | _ -> false



let rec eval ctx e0 = burn (); traceEval e0; match e0 with
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
  | EAnd (e1, e2)        -> andFormula (eval ctx e1, eval ctx e2)
  | EOr (e1, e2)         -> orFormula (eval ctx e1, eval ctx e2)
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
  | ENat                 -> VNat
  | EZero                -> VZero
  | ESucc e              -> VSucc (eval ctx e)
  | EIndNat (c, z, s)    -> VIndNat (eval ctx c, eval ctx z, eval ctx s)
  | EW (a, (p, b))       -> let t = eval ctx a in W (t, (fresh p, closByVal ctx p t b))
  | ESup (a, b)          -> VSup (eval ctx a, eval ctx b)
  | EIndW (a, b, c)      -> VIndW (eval ctx a, eval ctx b, eval ctx c)
  | EIm e                -> VIm (eval ctx e)
  | EInf e               -> inf (eval ctx e)
  | EJoin e              -> join (eval ctx e)
  | EIndIm (a, b)        -> VIndIm (eval ctx a, eval ctx b)
  | EFla e               -> VFla (eval ctx e)
  | EFlaUnit e           -> flaunit (eval ctx e)
  | EFlaCounit e         -> flacounit (eval ctx e)
  | EIndFla (a, b)       -> VIndFla (eval ctx a, eval ctx b)
  | ECoequ (a, b, f, g)  -> VCoequ (eval ctx a, eval ctx b, eval ctx f, eval ctx g)
  | EIota2 (a, b, f, g, c) -> VIota2 (eval ctx a, eval ctx b, eval ctx f, eval ctx g, eval ctx c)
  | EResp (a, b, f, g, c) -> VResp (eval ctx a, eval ctx b, eval ctx f, eval ctx g, eval ctx c)
  | EIndCoequ (a, b, f, g, x, i, rho) -> VIndCoequ (eval ctx a, eval ctx b, eval ctx f, eval ctx g, eval ctx x, eval ctx i, eval ctx rho)
  | EDisc (s, a) -> VDisc (eval ctx s, eval ctx a)
  | EBase (s, a, x) -> VBase (eval ctx s, eval ctx a, eval ctx x)
  | EHub (s, a, f) -> VHub (eval ctx s, eval ctx a, eval ctx f)
  | ESpoke (s, a, f, x) -> VSpoke (eval ctx s, eval ctx a, eval ctx f, eval ctx x)
  | EIndDisc (s, a, x, nc, nh, ns') -> VIndDisc (eval ctx s, eval ctx a, eval ctx x, eval ctx nc, eval ctx nh, eval ctx ns')


and appFormula v x = match v with
  | VPLam f -> app (f, x)
  | VResp (a, b, f, g, c) ->
    if orEq x vzero then VIota2 (a, b, f, g, app (f, c)) else
    if orEq x vone then VIota2 (a, b, f, g, app (g, c)) else
    VAppFormula (v, x)
  | VSpoke (s, a, f, y) ->
    if orEq x vzero then VHub (s, a, f) else
    if orEq x vone then app (f, y) else
    VAppFormula (v, x)
  | VKan _ -> if orEq x vzero || orEq x vone then VKan Z.zero else VAppFormula (v, x)
  | _       ->
    begin try
      let (_, u0, u1) = extPathP (inferV v) in
      if orEq x vzero then u0 else if orEq x vone then u1 else VAppFormula (v, x)
    with _ -> VAppFormula (v, x)
    end


and border xs v = mkSystem (List.map (fun mu -> (mu, upd mu v)) xs)

and partialv t r = VPartialP (VSystem (border (solve r One) t) , r)

and upd mu = act (Env.map dir mu)

and transp p phi u0 = match phi with
  | r when orEq r vone -> u0
  | _ ->
  match p with
  | VPLam (VLam (VI, (i, g))) -> transport i (g (Var (i, VI))) phi u0
  | _ -> VApp (VTransp (p, phi), u0)

and glue r u a = match r, a with
  | r, _ when orEq r vone -> vsnd (vsnd (app (u, VRef vone)))
  | _, VUnglue (_, _, b) -> b
  | _, _ -> VGlueElem (r, u, a)

and unglue r u b = match r, u, b with
  | r, _, _ when orEq r vone -> app (vfst (vsnd (app (u, VRef vone))), b)
  | _, _, VGlueElem (_, _, a) -> ouc a
  | _, _, _ -> VUnglue (r, u, b)

and transport i p phi u0 =
  if not (mem i p) then u0 else
  let h = (Hashtbl.hash_param 1000 10000 (i, p, phi, u0)) land (transport_cache_size - 1) in
  let (i', p', phi', u0', r) = transport_cache.(h) in
  let r = if i == i' && p == p' && phi == phi' && u0 == u0' then (incr trans_hits; r) else
  begin
    incr trans_misses;
    match p, phi, u0 with
  | VApp (VApp (VGlue a, phi_glue), sys), phi, u0 ->
    let is = match i with Ident (s, _) -> s | _ -> "" in
    let d0 = match phi with VDir d -> d | _ -> Zero in
    let e0 = ref None in
    let e1 = ref None in
    let d1 = if d0 = Zero then One else Zero in
    begin match sys with
    | VSystem s ->
      System.iter (fun mu e ->
        match Env.find_opt i mu with
        | Some d ->
          if d = d0 then e0 := Some e
          else if d = d1 then e1 := Some e
        | None -> ()
      ) s
    | _ -> ()
    end;
    let res = match !e0, !e1 with
      | Some f0, Some f1 ->
        let (_, ei0) = eta f0 in let (f0, _) = eta ei0 in
        let (_, ei1) = eta f1 in let (_, w1) = eta ei1 in
        Some (vfst (vfst (app (w1, app (f0, u0)))))
      | Some f0, None ->
        let (_, ei0) = eta f0 in let (f0, _) = eta ei0 in
        Some (app (f0, u0))
      | None, Some f1 ->
        let (_, ei1) = eta f1 in let (_, w1) = eta ei1 in
        Some (vfst (vfst (app (w1, u0))))
      | None, None -> None
    in
    begin match res with
    | Some v -> v
    | None ->
    let u = match sys with VSystem s -> s | _ -> System.empty in
    let u' = System.map eta (forall i u) in let psi' = getFormulaV u' in

    let t1 = System.map (fun u -> transFill i (fst u) phi u0 vone) u' in
    let ts = System.map (fun u -> app (vfst (snd u), transFill i (fst u) phi u0 (dim i))) u' in

    let uj k = bimap (fun j -> if i = j then k else dim j) upd u in
    let uzero = uj vzero in let a0 = unglue (getFormulaV uzero) (VSystem uzero) u0 in

    let phi1 = solve phi One in let ksi = orFormula (phi, psi') in
    let a1 = comp (fun j -> act0 i j a) ksi i (VSystem (unionSystem (border phi1 a0) ts)) a0 in

    let fib = System.map (fun x -> VPair (ref None, x, idp a1))
      (unionSystem (border phi1 u0) t1) in

    let b = act0 i vone p in
    let u1 = System.map eta (uj vone) in
    let fib' = System.map (fun (t, w) ->
      (t, w, contr (fiber b t (vfst w) a1) (app (vsnd w, a1)) ksi fib)) u1 in

    let chi = getFormulaV u1 in
    let a1' = homcom b (orFormula (chi, phi)) i
      (VSystem (unionSystem (System.map (fun (_, _, p) ->
        appFormula (vsnd p) (dim i)) fib') (border phi1 a1))) a1 in

    glue chi (VSystem (System.map (fun p -> let (t, w, u) = p in
      pairv t (pairv w (vfst u))) fib')) a1'
    end
  (* transp p 1 u₀ ~> u₀ *)
  | _, phi, u0 when orEq phi vone -> u0
  | p, _, u0 when not (mem i p) -> u0
  | VCoequ (a, b, f, g), phi, u0 ->
    let j = freshName "ι" in
    let a1 = act0 i vone a in
    let b1 = act0 i vone b in
    let f1 = act0 i vone f in
    let g1 = act0 i vone g in
    app (VIndCoequ (a, b, f, g, VLam (VCoequ (a, b, f, g), (freshName "v", fun _ -> VCoequ (a1, b1, f1, g1))),
      VLam (b, (freshName "v", fun v -> VIota2 (a1, b1, f1, g1, transport i b phi v))),
      VLam (a, (freshName "v", fun v -> VPLam (VLam (VI, (j, fun j -> appFormula (VResp (a1, b1, f1, g1, transport i a phi v)) j)))))), u0)
  | VDisc (s, a), phi, u0 ->
    let a1 = act0 i vone a in
    let s1 = act0 i vone s in
    app (VIndDisc (s, a, VLam (VDisc (s, a), (freshName "v", fun _ -> VDisc (s1, a1))),
      VLam (a, (freshName "v", fun v -> VBase (s1, a1, transport i a phi v))),
      VLam (VPi (s, (Irrefutable, fun _ -> VDisc (s, a))), (freshName "f", fun _ ->
        VLam (VPi (s, (Irrefutable, fun _ -> VDisc (s1, a1))), (freshName "f'", fun f' ->
          VLam (s, (freshName "v", fun _ -> VHub (s1, a1, f'))))))),
      VLam (VPi (s, (Irrefutable, fun _ -> VDisc (s, a))), (freshName "f", fun _ ->
        VLam (VPi (s, (Irrefutable, fun _ -> VDisc (s1, a1))), (freshName "f'", fun f' ->
          VLam (s, (freshName "v", fun v -> VLam (VI, (freshName "j", fun j ->
            VAppFormula (VSpoke (s1, a1, f', transport i s phi v), j)))))))))), u0)
  | VIndCoequ (a, b, f, g, motive, i_base, p_loop), phi, u0 ->
    let a' = act0 i vone a in let b' = act0 i vone b in
    let f' = act0 i vone f in let g' = act0 i vone g in
    let motive' = act0 i vone motive in
    let i_base' = VLam (b', (freshName "b", fun x -> transport i (app (motive, VIota2 (a, b, f, g, x))) phi (app (i_base, x)))) in
    let p_loop' = VLam (a', (freshName "a", fun x -> transport i (VApp (VApp (VPathP (VPLam (VLam (VI, (freshName "j", fun j -> app (motive, VAppFormula (VResp (a, b, f, g, x), j)))))), app (i_base, app (f, x))), app (i_base, app (g, x)))) phi (app (p_loop, x)))) in
    VIndCoequ (a', b', f', g', motive', i_base', p_loop')

  | VIndDisc (s, a, motive, nc, nh, ns), phi, u0 ->
    let s' = act0 i vone s in let a' = act0 i vone a in
    let motive' = act0 i vone motive in
    let nc' = VLam (a', (freshName "a", fun x -> transport i (app (motive, VBase (s, a, x))) phi (app (nc, x)))) in
    let nh' = VLam (VPi (s, (Irrefutable, fun _ -> VDisc (s, a))), (freshName "f", fun f ->
       let motive_f = VLam (s, (freshName "s", fun s -> app (motive, app (f, s)))) in
       transport i (app (nh, f)) phi (app (nh, f)))) in
    VIndDisc (s', a', motive', nc', nh', ns)

  | VIndNat (c, z, s) as p, phi, u0 ->
    let c' = act0 i vone c in
    let z' = transport i (app (c, VZero)) phi z in
    let s' = VLam (VNat, (freshName "n", fun n -> VLam (app (c', n), (freshName "ih", fun ih ->
       transport i (app (c, VSucc n)) phi (app (app (s, n), ih)))))) in
    VIndNat (c', z', s')

  | VIndBool c as p, phi, u0  -> VIndBool (act0 i vone c)
  | VIndUnit c as p, phi, u0  -> VIndUnit (act0 i vone c)
  | VIndEmpty c as p, phi, u0 -> VIndEmpty (act0 i vone c)
  | VHComp (VKan _, _, sys, u0), phi, a ->
     let u = match sys with VSystem s -> s | _ -> System.empty in
     let u' = System.map eta (forall i u) in
     let psi' = getFormulaV u' in
     let phi1 = solve phi One in
     let t1_and_ts = System.map (fun u ->
       let tf j = transFill i (fst u) phi u0 j in
       (tf vone, app (vfst (snd u), tf (dim i)))) u' in
     let t1 = System.map fst t1_and_ts in
     let ts = System.map snd t1_and_ts in
     let uj k = bimap (fun j -> if i = j then k else dim j) upd u in
     let uzero = uj vzero in
     let a0 = unglue (getFormulaV uzero) (VSystem uzero) a in
     let ksi = orFormula (phi, psi') in
     let a1 = comp (fun j -> act0 i j u0) ksi i (VSystem (unionSystem (border phi1 a0) ts)) a0 in
     let fib = System.map (fun x -> VPair (ref None, x, idp a1)) (unionSystem (border phi1 a) t1) in
     let b = act0 i vone u0 in
     let u1 = System.map eta (uj vone) in
     let fib' = System.map (fun (t, w) ->
       (t, w, contr (fiber b t (vfst w) a1) (app (vsnd w, a1)) ksi fib)) u1 in
     let chi = getFormulaV u1 in
     homcom b (orFormula (chi, phi)) i (VSystem (unionSystem (System.map (fun (_, _, p) -> appFormula (vsnd p) (dim i)) fib') (border phi1 a1))) a1
  (* transp (<_> U) i A ~> A *)
  | VKan _, _, _ -> u0
  (* transp (<_> 𝟎) i u₀ ~> u₀ *)
  | VEmpty, _, _ -> u0
  (* transp (<_> 𝟏) i u₀ ~> u₀ *)
  | VUnit, _, _ -> u0
  (* transp (<_> 𝟐) i u₀ ~> u₀ *)
  | VBool, _, _ -> u0
  | VNat, _, _ -> u0
  | VFla t, _, VFlaUnit a -> VFlaUnit (transport i t phi a)
  | VPi (t, (x, b)), _, _ ->
    if not (mem i t) then
      VLam (t, (x, fun x -> transport i (b x) phi (app (u0, x))))
    else
      let x_id = fresh x in
      let j = freshName "ι" in let k = freshName "κ" in
      VLam (act0 i vone t, (x_id, fun x ->
        let v = transFill j (act0 i (VNeg (dim j)) t) phi x in
        transport k (swap i k (b (v (VNeg (dim k)))))
          phi (app (u0, v vone))))
  | VSig (t, (x, b)), _, _ ->
    if not (mem i t) then
      let v1 = vfst u0 in
      VPair (ref None, v1, transport i (b v1) phi (vsnd u0))
    else
      let j = freshName "ι" in let k = freshName "κ" in
      let v1 = transFill j (swap i j t) phi (vfst u0) in
      let v2 = transport k (swap i k (b (v1 (dim k)))) phi (vsnd u0) in
      VPair (ref None, v1 vone, v2)
  | VApp (VApp (VPathP p, v), w), _, _ ->
    let j = freshName "ι" in let k = freshName "κ" in
    VPLam (VLam (VI, (j, fun j ->
      let uj = appFormula u0 j in let r = orFormula (phi, orFormula (j, negFormula j)) in
      comp (fun k -> appFormula (act0 i k p) j) r k
        (VSystem (unionSystem (border (solve phi One) uj)
                 (unionSystem (border (solve j Zero) (swap i k v))
                               (border (solve j One)  (swap i k w))))) uj)))
  | W (t, (x, b)), _, VApp (VApp (VSup _, a), f) ->
    let j = freshName "ι" in let k = freshName "κ" in let v1 = transFill j (swap i j t) phi a in
    let v2 = transport k (swap i k (implv (b (v1 (dim k))) (W (t, (x, b))))) phi f in let t' = act0 i vone t in
    VApp (VApp (VSup (t', VLam (t', (fresh x, b >> act0 i vone))), v1 vone), v2)
  | VApp (VApp (VGlue _, _), _), _, _
  | VApp (VApp (VId _, _), _), _, _ ->
    let j = freshName "ι" in
    comp (fun j -> act0 i j p) phi i (VSystem System.empty) u0
  | VIm t, _, VInf a -> inf (transport i t phi a)
  | t, _, _ -> VApp (VTransp (VPLam (VLam (VI, (i, fun j -> act0 i j t))), phi), u0)
  (* transp (<_> U) i A ~> A *)
  | VKan _, _, _ -> u0
  (* transp (<_> 𝟎) i u₀ ~> u₀ *)
  | VEmpty, _, _ -> u0
  (* transp (<_> 𝟏) i u₀ ~> u₀ *)
  | VUnit, _, _ -> u0
  (* transp (<_> 𝟐) i u₀ ~> u₀ *)
  | VBool, _, _ -> u0
  | VNat, _, _ -> u0
  | VFla t, _, VFlaUnit a -> VFlaUnit (transport i t phi a)
  (* transp (<i> Π (x : A i), B i x) φ u₀ ~>
     λ (x : A 1), transp (<i> B i (transFill (<j> A -j) φ x -i)) φ
      (u₀ (transFill (<j> A -j) φ x 1)) *)
  | VPi (t, (x, b)), _, _ ->
    if not (mem i t) then
      VLam (t, (x, fun x -> transport i (b x) phi (app (u0, x))))
    else
      let x_id = fresh x in
      let j = freshName "ι" in let k = freshName "κ" in
      VLam (act0 i vone t, (x_id, fun x ->
        let v = transFill j (act0 i (VNeg (dim j)) t) phi x in
        transport k (swap i k (b (v (VNeg (dim k)))))
          phi (app (u0, v vone))))
  | VSig (t, (x, b)), _, _ ->
    if not (mem i t) then
      let v1 = vfst u0 in
      VPair (ref None, v1, transport i (b v1) phi (vsnd u0))
    else
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
      let uj = appFormula u0 j in let r = orFormula (phi, orFormula (j, negFormula j)) in
      comp (fun k -> appFormula (act0 i k p) j) r k
        (VSystem (unionSystem (border (solve phi One) uj)
                 (unionSystem (border (solve j Zero) (swap i k v))
                               (border (solve j One)  (swap i k w))))) uj)))

    (* ignore "VHCOMP TRANSPORT" []; *)

  (* transp (<i> W (x : A i), B i x) φ (sup (A 0) (B 0) a f) ~>
     sup (A 1) (B 1) (transp (<i> A i) φ a)
         (transp (<i> B i (transFill (<i> A i) φ a i) → (W (x : A i), B i x)) φ f) *)
  | W (t, (x, b)), _, VApp (VApp (VSup _, a), f) ->
    (* if conv (act0 i vone p) p then u0 else ??? *)
    let j = freshName "ι" in let k = freshName "κ" in let v1 = transFill j (swap i j t) phi a in
    let v2 = transport k (swap i k (implv (b (v1 (dim k))) (W (t, (x, b))))) phi f in let t' = act0 i vone t in
    VApp (VApp (VSup (t', VLam (t', (fresh x, b >> act0 i vone))), v1 vone), v2)
  (* transp (<i> ℑ (A i)) 0 (ℑ-unit a) ~> ℑ-unit (transp (<i> A i) 0 a) *)
  | VApp (VApp (VGlue _, _), _), _, _
  | VApp (VApp (VId _, _), _), _, _ ->
    let j = freshName "ι" in
    comp (fun j -> act0 i j p) phi i (VSystem System.empty) u0
  | VIm t, _, VInf a -> inf (transport i t phi a)
  | t, _, _ -> VApp (VTransp (VPLam (VLam (VI, (i, fun j -> act0 i j t))), phi), u0)
  end in
  transport_cache.(h) <- (i, p, phi, u0, r);
  r

and transFill i p phi u0 j = let (k, _, _) = freshDim () in
  transport k (act0 i (andFormula (dim k, j)) p) (orFormula (phi, negFormula j)) u0

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
                appFormula p (andFormula (i, j)))))))))))))))

and idtoeqv i e =
  if not (mem i e) then idEquiv e else
  let a = act0 i vzero e in
  match e with
  | VApp (VApp (VGlue _, phi), VSystem sys) ->
    (* Specialized idtoeqv for Glue types to avoid generic transport over equiv *)
    transport i (equiv a e) vzero (idEquiv a) (* TODO: implement direct Glue equiv *)
  | _ -> transport i (equiv a e) vzero (idEquiv a)

and walk f r = function
  | VSystem ts -> System.mapi (fun mu -> f >> upd mu) ts
  | t          -> mkSystem (List.map (fun mu ->
    (mu, upd mu (f (app (upd mu t, VRef vone))))) (solve r One))

and structural_homcom motive r_comp i u_comp u0_comp t =
  match app (motive, VRef vone) with
  | VPi (t', (p', b')) ->
    let walked = walk (fun v -> v) r_comp u_comp in
    VLam (t', (fresh p', fun y -> homcom (b' y) r_comp i
    (VSystem (System.map (fun v -> app (v, y)) walked)) (app (u0_comp, y))))
  | VSig (t', (_, b')) -> let k = freshName "κ" in
    let sys1 = walk (vfst >> act0 i (dim k)) r_comp u_comp in
    let v1 = hfill t' r_comp k (VSystem sys1) (vfst u0_comp) in
    let sys2 = walk vsnd r_comp u_comp in
    let v2 = comp (v1 >> b') r_comp i (VSystem sys2) (vsnd u0_comp) in
    VPair (ref None, v1 vone, v2)
  | VApp (VApp (VPathP t', v), w) ->
    let j = freshName "ι" in
    let walked = walk (fun v' -> v') r_comp u_comp in
    VPLam (VLam (VI, (j, fun j ->
      homcom (appFormula t' j) (orFormula (r_comp, orFormula (j, negFormula j))) i
          (VSystem (unionSystem (System.map (flip appFormula j) walked)
                   (unionSystem (border (solve j One)  w)
                                (border (solve j Zero) v))))
          (appFormula u0_comp j))))
  | _ -> VHComp (t, r_comp, VLam (VI, (i, fun j -> VSystem (walk (act0 i j) r_comp u_comp))), u0_comp)

and homcom t r i u u0 =
  match r with
  | r when orEq r vone -> app (act0 i vone u, VRef vone)
  | _ -> 
  let sys = match u with VSystem s -> s | _ -> System.empty in
  if solve r One = [] && System.is_empty sys then u0 else
  match t, r, u, u0 with
  (* hcomp (Π (x : A), B x) φ u u₀ ~> λ (x : A), hcomp (B x) φ (λ (i : I), [φ → u i 1=1 x]) (u₀ x) *)
  | VPi (t, (x, b)), _, _, _ ->
    let sys = walk (fun v -> v) r u in
    VLam (t, (fresh x, fun y -> homcom (b y) r i
      (VSystem (System.map (fun v -> app (v, y)) sys)) (app (u0, y))))
   (* hcomp (Σ (x : A), B x) φ u u₀ ~>
     (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 1,
      comp (λ i, B (hfill A φ (λ (k : I), [(r = 1) → (u k 1=1).1]) u₀.1 i)) φ
        (λ (k : I), [(r = 1) → (u k 1=1).2]) u₀.2) *)
  | VSig (t, (_, b)), _, _, _ -> let k = freshName "κ" in
    let sys1 = walk (vfst >> act0 i (dim k)) r u in
    let v1 = hfill t r k (VSystem sys1) (vfst u0) in
    let sys2 = walk vsnd r u in
    let v2 = comp (v1 >> b) r i (VSystem sys2) (vsnd u0) in
    VPair (ref None, v1 vone, v2)
  (* hcomp (PathP A v w) φ u u₀ ~> <j> hcomp (A @ j) (λ (i : I),
      [(r = 1) → u i 1=1 @ j, (j = 0) → v, (j = 1) → w]) (u₀ @ j) *)
  | VApp (VApp (VPathP t, v), w), _, _, _ ->
    let j = freshName "ι" in
    let walked = walk (fun v -> v) r u in
    VPLam (VLam (VI, (j, fun j ->
      homcom (appFormula t j) (orFormula (r, orFormula (j, negFormula j))) i
          (VSystem (unionSystem (System.map (flip appFormula j) walked)
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

    let a1 = homcom a (orFormula (r, phi)) i (VSystem (unionSystem
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
          app (f, transport j (b (act0 i (orFormula (negFormula (dim j), dim i)) a)) vzero y)))) u'))
      (VLam (b a1, (y, fun y -> app (f0, transport j (b (a' (VNeg (dim j)))) vzero y)))) in
    VApp (VApp (VSup (t, b'), a1), f1)
  | VIm t, _, VSystem u, VInf u0 when System.for_all (fun _ -> isInf) u ->
    VInf (homcom t r i (VSystem (System.map extInf u)) u0)
  | VNat, _, VSystem u, VZero when System.for_all (fun _ v -> isZero v) u -> VZero
  | VNat, _, VSystem u, VSucc u0 when System.for_all (fun _ v -> isSucc v) u ->
    VSucc (homcom VNat r i (VSystem (System.map extSucc u)) u0)
  | VCoequ (a, b, f, g), _, VSystem u, VIota2 (_, _, _, _, u0) when System.for_all (fun _ v -> isIota2 v) u ->
    VIota2 (a, b, f, g, homcom b r i (VSystem (System.map extIota2 u)) u0)
  | VDisc (s, a), _, VSystem u, VBase (_, _, u0) when System.for_all (fun _ v -> isBase v) u ->
    VBase (s, a, homcom a r i (VSystem (System.map extBase u)) u0)
  | VDisc (s, a), _, VSystem u, VHub (_, _, f0) when System.for_all (fun _ v -> isHub v) u ->
    VHub (s, a, homcom (implv s (VDisc (s, a))) r i (VSystem (System.map extHub u)) f0)
  | VFla t, _, VSystem u, VFlaUnit u0 when System.for_all (fun _ v -> isFlaUnit v) u ->
    VFlaUnit (homcom t r i (VSystem (System.map extFlaUnit u)) u0)
  | VCoequ (a, b, f, g), _, VSystem u, VAppFormula (VResp (_, _, _, _, u0), r) when System.for_all (fun _ v -> isRespFormula v) u ->
    VAppFormula (VResp (a, b, f, g, homcom a r i (VSystem (System.map extRespFormula u)) u0), r)
  | VDisc (s, a), _, VSystem u, VAppFormula (VSpoke (_, _, f, y), r) when System.for_all (fun _ v -> isSpokeFormula v) u ->
    VAppFormula (VSpoke (s, a, homcom (implv s (VDisc (s, a))) r i (VSystem (System.map (fun v -> fst (extSpokeFormula v)) u)) f,
                               homcom s r i (VSystem (System.map (fun v -> snd (extSpokeFormula v)) u)) y), r)
  | VApp (VIndCoequ (a, b, f, g, motive, i_base, p_loop), x), r_comp, u_comp, u0_comp ->
    (match app (motive, VRef vone) with VPre _ | VKan _ ->
      let j = freshName "ι" in
      let i' = VPLam (VLam (VI, (j, fun j -> homcom (app (i_base, j)) r_comp i u_comp u0_comp))) in
      let p' = VPLam (VLam (VI, (j, fun j -> homcom (app (p_loop, j)) r_comp i u_comp u0_comp))) in
      VApp (VIndCoequ (a, b, f, g, motive, i', p'), x)
    | _ -> structural_homcom motive r_comp i u_comp u0_comp t)
  | VApp (VApp (VIndDisc (s, a, motive, nc, nh, ns'), z), x), r_comp, u_comp, u0_comp ->
    let (VLam (_, (_, g')) as motive_lam) = motive in
    (match g' (VRef vone) with
    | VPre _ | VKan _ ->
      let j = freshName "ι" in
      let nc' = VPLam (VLam (VI, (j, fun j -> homcom (app (nc, j)) r_comp i u_comp u0_comp))) in
      let nh' = VPLam (VLam (VI, (j, fun j -> homcom (app (nh, j)) r_comp i u_comp u0_comp))) in
      let ns'' = VPLam (VLam (VI, (j, fun j -> homcom (app (ns', j)) r_comp i u_comp u0_comp))) in
      let z' = VPLam (VLam (VI, (j, fun j -> homcom (app (z, j)) r_comp i u_comp u0_comp))) in
      VApp (VApp (VIndDisc (s, a, motive_lam, nc', nh', ns''), z'), x)
    | _ -> structural_homcom motive_lam r_comp i u_comp u0_comp t)
  | VApp (VIndNat (c, z, s), n), r_comp, u_comp, u0_comp ->
    (match app (c, VRef vone) with
    | VPre _ | VKan _ ->
      let j = freshName "ι" in
      let z' = homcom z r_comp i u_comp u0_comp in
      let s' = VPLam (VLam (VI, (j, fun j -> homcom (app (s, j)) r_comp i u_comp u0_comp))) in
      VApp (VIndNat (c, z', s'), n)
    | _ -> structural_homcom c r_comp i u_comp u0_comp t)
  | VApp (VIndBool c, n), r_comp, u_comp, u0_comp  -> structural_homcom c r_comp i u_comp u0_comp t
  | VApp (VIndUnit c, n), r_comp, u_comp, u0_comp  -> structural_homcom c r_comp i u_comp u0_comp t
  | VApp (VIndEmpty c, n), r_comp, u_comp, u0_comp -> structural_homcom c r_comp i u_comp u0_comp t
  | _, _, _, _ -> VHComp (t, r, VLam (VI, (i, fun j -> VSystem (walk (act0 i j) r u))), u0)

and comp t r i u u0 =
  let j = freshName "ι" in
  let tj = t (dim j) in
  if not (mem j tj) then homcom (t vone) r i u u0 else
  homcom (t vone) r i (VSystem (walk (transport j (t (orFormula (dim i, dim j))) (dim i)) r u))
    (transport j (t (dim j)) vzero u0)

and hfill t r i u u0 j = let k = freshName "κ" in
  homcom t (orFormula (negFormula j, r)) k
    (VSystem (unionSystem (walk (act0 i (andFormula (dim k, j))) r u)
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
  let ctx' = match v with
  | Var (x, t) -> if Env.mem x ctx then ctx else upLocal ctx x t v
  | _          -> ctx in
  eval (upLocal ctx' p t v) e

and app (v, x) =
  let h = (Hashtbl.hash_param 1000 10000 (v, x)) land (app_cache_size - 1) in
  let (v', x', r) = app_cache.(h) in
  let res = if v == v' && x == x' then (incr app_hits; r) else
  begin
    incr app_misses;
    burn ();
    match v, x with
  (* J A C a φ a (ref a) ~> φ *)
  | VApp (VApp (VApp (VApp (VJ _, _), _), f), _), VRef _ -> f
  (* Glue A 1 u ~> (u 1=1).1 *)
  | VApp (VGlue _, phi), u when orEq phi vone -> vfst (app (u, VRef vone))
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
  (* ind-nat C z s 0 ~> z *)
  | VIndNat (_, z, _), VZero -> z
  (* ind-nat C z s (succ n) ~> s n (app (VIndNat (c, z, s), n)) *)
  | VIndNat (c, z, s), VSucc n -> app (app (s, n), app (VIndNat (c, z, s), n))
  (* ind-ℑ A B f (ℑ-unit a) ~> f a *)
  | VApp (VIndIm _, f), VInf a -> app (f, a)
  | VApp (VIndFla _, f), VFlaUnit a -> app (f, a)
  | VApp (VIndIm (a, b), f), VHComp (_, r, u, u0) ->
    let g x = app (VApp (VIndIm (a, b), f), x) in
    let i = freshName "ι" in let k = freshName "κ" in
    comp (fun j -> VIm (app (b, hfill (VIm a) r i (app (u, dim i)) u0 j))) r k
      (VSystem (walk g r (app (u, dim k)))) (g u0)
  (* ind-ℑ A B (λ _, b) x ~> b *)
  | VApp (VIndIm (a, b), VLam (t, (x, g))), v -> let u = g (Var (x, t)) in
    if mem x u then VApp (VApp (VIndIm (a, b), VLam (t, (x, g))), v) else u
  | VApp (VIndFla (a, b), VLam (t, (x, g))), v -> let u = g (Var (x, t)) in
    if mem x u then VApp (VApp (VIndFla (a, b), VLam (t, (x, g))), v) else u
  (* ind-nat C z s (hcomp Nat r u u0) ~> ... *)
  | VIndNat (c, _, _) as ind, VHComp (t, r, sys, u0) ->
    let g_ind v = app (ind, v) in
    let iota = freshName "iota" in
    let kappa = freshName "kappa" in
    comp (fun j -> app (c, hfill t r iota (app (sys, dim iota)) u0 j)) r kappa
      (VSystem (walk g_ind r (app (sys, dim kappa)))) (g_ind u0)
  (* coequ-ind A B f g X i rho (ι₂ b) ~> i b *)
  | VIndCoequ (_, _, _, _, _, i, _), VIota2 (_, _, _, _, b) -> app (i, b)
  (* coequ-ind A B f g X i rho (resp a @ r) ~> rho a @ r *)
  | VIndCoequ (_, _, _, _, _, _, rho), VAppFormula (VResp (_, _, _, _, a), r) ->
    appFormula (app (rho, a)) r
  | VIndCoequ (_, _, _, _, _, _, rho), VResp (_, _, _, _, a) ->
    app (rho, a)
  (* coequ-ind A B f g X i rho (hcomp A' r u u0) ~> ... *)
  | VIndCoequ (_, _, _, _, x, _, _) as ind, VHComp (t, r, sys, u0) ->
    let g_ind v = app (ind, v) in
    let iota = freshName "iota" in
    let kappa = freshName "kappa" in
    let tj = if is_constant_motive x then let v = app (x, VHole) in fun _ -> v
             else fun j -> app (x, hfill t r iota (app (sys, dim iota)) u0 j) in
    comp tj r kappa (VSystem (walk g_ind r (app (sys, dim kappa)))) (g_ind u0)
  | VIndDisc (s, a, x, nc, nh, ns), VBase (_, _, v) -> app (nc, v)
  | VIndDisc (s, a, x, nc, nh, ns), VHub (_, _, f) ->
    let nF = VLam (s, (freshName "s", fun v -> app (VIndDisc (s, a, x, nc, nh, ns), app (f, v)))) in
    app (app (nh, f), nF)
  | VIndDisc (s, a, x, nc, nh, ns), VAppFormula (VSpoke (_, _, f, y), r) ->
    let nF = VLam (s, (freshName "s", fun v -> app (VIndDisc (s, a, x, nc, nh, ns), app (f, v)))) in
    appFormula (app (app (app (ns, f), nF), y)) r
  | VIndDisc (s, a, x, nc, nh, ns), VSpoke (_, _, f, y) ->
    let nF = VLam (s, (freshName "s", fun v -> app (VIndDisc (s, a, x, nc, nh, ns), app (f, v)))) in
    app (app (ns, f), nF)
  | VIndDisc (s, a, x', nc, nh, ns) as ind, VHComp (t, r, sys, u0) ->
    let g_ind v = app (ind, v) in
    let iota = freshName "iota" in
    let kappa = freshName "kappa" in
    let tj = if is_constant_motive x' then let v = app (x', VHole) in fun _ -> v
             else fun j -> app (x', hfill t r iota (app (sys, dim iota)) u0 j) in
    comp tj r kappa (VSystem (walk g_ind r (app (sys, dim kappa)))) (g_ind u0)
  | f, x -> VApp (f, x) end in
  app_cache.(h) <- (v, x, res);
  res

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
  | VAppFormula (f, x)       ->
    let (p, _, _) = match inferV f with
      | VKan _ -> (VLam (VI, (freshName "i", fun _ -> VKan Z.zero)), VKan Z.zero, VKan Z.zero)
      | v -> extPathP v in
    appFormula p x

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
  | VEmpty | VUnit | VBool | VNat -> VKan Z.zero
  | VStar -> VUnit | VFalse -> VBool | VTrue -> VBool | VZero -> VNat
  | VSucc n -> if conv (inferV n) VNat then VNat else raise (Internal (InferError (rbV v)))
  | VIndNat (c, _, _) ->
    let x = freshName "x" in
    VPi (VNat, (x, fun x -> app (c, x)))
  | VIndEmpty t -> implv VEmpty t
  | VIndUnit t -> recUnit t
  | VIndBool t -> recBool t
  | VSup (a, b) -> inferSup a b
  | VIndW (a, b, c) -> inferIndW a b c
  | VIm t -> inferV t
  | VInf v -> VIm (inferV v)
  | VJoin v -> extIm (inferV v)
  | VIndIm (a, b) -> inferIndIm a b
  | VFla t -> inferV t
  | VFlaUnit v -> VFla (inferV v)
  | VFlaCounit v -> extFla (inferV v)
  | VIndFla (a, b) -> inferIndFla a b
  | VCoequ (a, _, _, _) -> VKan (extSet (inferV a))
  | VIota2 (a, b, f, g, _) -> VCoequ (a, b, f, g)
  | VResp (a, b, f, g, c) ->
    let t = VCoequ (a, b, f, g) in
    let p = VPLam (VLam (VI, (freshName "i", fun _ -> t))) in
    VApp (VApp (VPathP p, VIota2 (a, b, f, g, app (f, c))), VIota2 (a, b, f, g, app (g, c)))
  | VIndCoequ (a, b, f, g, x, _, _) -> VPi (VCoequ (a, b, f, g), (freshName "z", fun z -> app (x, z)))
  | VDisc (_, a) -> VKan (extSet (inferV a))
  | VBase (s, a, _) -> VDisc (s, a)
  | VHub (s, a, _) -> VDisc (s, a)
  | VSpoke (s, a, f, y) ->
    let t = VDisc (s, a) in
    let p = VPLam (VLam (VI, (freshName "i", fun _ -> t))) in
    VApp (VApp (VPathP p, VHub (s, a, f)), app (f, y))
  | VIndDisc (s, a, x, nc, nh, ns) -> VPi (VDisc (s, a), (freshName "z", fun z -> app (x, z)))
  | VPLam _ | VPair _ | VHole -> raise (Internal (InferError (rbV v)))



and inferVTele g t x f = g (inferV t) (inferV (f (Var (x, t))))

and recUnit t = let x = freshName "x" in
  implv (app (t, VStar)) (VPi (VUnit, (x, fun x -> app (t, x))))

and recBool t = let x = freshName "x" in
  implv (app (t, VFalse)) (implv (app (t, VTrue))
    (VPi (VBool, (x, fun x -> app (t, x)))))

and recNat t = let x = freshName "x" in
  implv (app (t, VZero)) (implv (VPi (VNat, (freshName "n", fun n -> implv (app (t, n)) (app (t, VSucc n)))))
    (VPi (VNat, (x, fun x -> app (t, x)))))

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

and inferIndFla a b =
  implv (VPi (a, (freshName "a", fun x -> VFla (app (b, flaunit x)))))
        (VPi (VFla a, (freshName "a", fun x -> VFla (app (b, x)))))

and inferInc t r = let a = freshName "a" in
  VPi (t, (a, fun v -> VSub (t, r, VSystem (border (solve r One) v))))

and inferGlue t = let (r, _, _) = freshDim () in let k = inferV t in
  VPi (VI, (r, fun r -> implv (partialv (equivSingl t) r) k))

and inferGlueElem r u t =
  VApp (VApp (VGlue t, r), VSystem (walk (fun v -> VPair (ref None, vfst v, vfst (vsnd v))) r u))

and inferJ v t =
  let x = freshName "x" in let y = freshName "y" in let pi = freshName "P" in let p = freshName "p" in
  let k = extSet t in
  let t = VPi (v, (x, fun x -> VPi (v, (y, fun y -> implv (idv v x y) (VPre k))))) in

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



and act rho v =
  if Env.is_empty rho then v else
  let s = get_support v in
  if not (IdentSet.exists (fun i -> Env.mem i rho) s) then v else
  let h = (Hashtbl.hash_param 100 1000 (rho, v)) land (act_cache_size - 1) in
  let (rho', v', r) = act_cache.(h) in
  if v == v' && (rho == rho' || Env.equal (=) rho rho') then r else
  let r = act_internal rho v in
  act_cache.(h) <- (rho, v, r);
  r

and act_internal rho v = match v with
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
  | VAnd (u, v)          -> andFormula (act rho u, act rho v)
  | VOr (u, v)           -> orFormula (act rho u, act rho v)
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
  | VNat                 -> VNat
  | VZero                -> VZero
  | VSucc v              -> VSucc (act rho v)
  | VIndNat (c, z, s)    -> VIndNat (act rho c, act rho z, act rho s)
  | W (t, (x, g))        -> W (act rho t, (x, g >> act rho))
  | VSup (a, b)          -> VSup (act rho a, act rho b)
  | VIndW (a, b, c)      -> VIndW (act rho a, act rho b, act rho c)
  | VIm t                -> VIm (act rho t)
  | VInf v               -> inf (act rho v)
  | VJoin v              -> join (act rho v)
  | VIndIm (a, b)        -> VIndIm (act rho a, act rho b)
  | VCoequ (a, b, f, g)  -> VCoequ (act rho a, act rho b, act rho f, act rho g)
  | VIota2 (a, b, f, g, c) -> VIota2 (act rho a, act rho b, act rho f, act rho g, act rho c)
  | VResp (a, b, f, g, c) -> VResp (act rho a, act rho b, act rho f, act rho g, act rho c)
  | VIndCoequ (a, b, f, g, x, i, p) -> VIndCoequ (act rho a, act rho b, act rho f, act rho g, act rho x, act rho i, act rho p)
  | VDisc (s, a) -> VDisc (act rho s, act rho a)
  | VBase (s, a, x) -> VBase (act rho s, act rho a, act rho x)
  | VHub (s, a, f) -> VHub (act rho s, act rho a, act rho f)
  | VSpoke (s, a, f, x) -> VSpoke (act rho s, act rho a, act rho f, act rho x)
  | VIndDisc (s, a, x, nc, nh, ns) -> VIndDisc (act rho s, act rho a, act rho x, act rho nc, act rho nh, act rho ns)
  | VFla t               -> VFla (act rho t)
  | VFlaUnit v           -> flaunit (act rho v)
  | VFlaCounit v         -> flacounit (act rho v)
  | VIndFla (a, b)       -> VIndFla (act rho a, act rho b)


and actVar rho i = match Env.find_opt i rho with
  | Some v -> v
  | None   -> Var (i, VI)

and act0 i j = act (Env.add i j Env.empty)

and conv v1 v2 = traceConv v1 v2;
  if v1 == v2 then true else
  let h = (Hashtbl.hash_param 1000 10000 (v1, v2)) land (conv_cache_size - 1) in
  let (v1', v2', r) = conv_cache.(h) in
  if (v1 == v1' && v2 == v2') || (v1 == v2' && v2 == v1') then (incr conv_hits; r) else
  (incr conv_misses;
  let r = conv_internal v1 v2 in
  conv_cache.(h) <- (v1, v2, r);
  r)

and conv_internal v1 v2 =
  burn ();
  ignore (v1, v2);
  begin
    match v1, v2 with
    | VKan u, VKan v -> ieq u v
    | VPair (_, a, b), VPair (_, c, d) -> conv a c && conv b d
    | VPair (_, a, b), v | v, VPair (_, a, b) -> conv (vfst v) a && conv (vsnd v) b
    | VPi  (a, (p, f)), VPi  (b, (_, g))
    | VSig (a, (p, f)), VSig (b, (_, g))
    | W    (a, (p, f)), W    (b, (_, g)) ->
      conv a b && (f == g || (incr conv_depth; let x = Var (Ident ("__conv__", Int64.of_int !conv_depth), a) in let r = conv (f x) (g x) in decr conv_depth; r))
    | VLam (a, (p, f)), VLam (b, (_, g)) ->
      conv a b && (f == g || conv a VEmpty || (incr conv_depth; let x = Var (Ident ("__conv__", Int64.of_int !conv_depth), a) in let r = conv (f x) (g x) in decr conv_depth; r))
    | VLam (a, (p, f)), b | b, VLam (a, (p, f)) ->
      conv a VEmpty || (incr conv_depth; let x = Var (Ident ("__conv__", Int64.of_int !conv_depth), a) in let r = conv (app (b, x)) (f x) in decr conv_depth; r)
    | VPre u, VPre v -> ieq u v
    | VPLam f, VPLam g -> (incr conv_depth; let i = Var (Ident ("__conv_dim__", Int64.of_int !conv_depth), VI) in let r = conv (app (f, i)) (app (g, i)) in decr conv_depth; r)
    | VPLam f, v | v, VPLam f -> (incr conv_depth; let i = Var (Ident ("__conv_dim__", Int64.of_int !conv_depth), VI) in let r = conv (appFormula v i) (app (f, i)) in decr conv_depth; r)
    | Var (u, _), Var (v, _) -> u = v
    | VApp (f, a), VApp (g, b) -> (f == g || conv f g) && (a == b || conv a b)
    | VFst x, VFst y | VSnd x, VSnd y -> x == y || conv x y
    | VPathP a, VPathP b -> a == b || conv a b
    | VPartialP (t1, r1), VPartialP (t2, r2) -> (t1 == t2 || conv t1 t2) && (r1 == r2 || conv r1 r2)
    | VAppFormula (f, x), VAppFormula (g, y) -> (f == g || conv f g) && (x == y || conv x y)
    | VSystem xs, VSystem ys -> xs == ys || System.equal conv xs ys
    | VSystem xs, x | x, VSystem xs -> System.for_all (fun alpha y -> conv (app (upd alpha x, VRef vone)) y) xs
    | VTransp (p, i), VTransp (q, j) -> (p == q || conv p q) && (i == j || conv i j)
    | VHComp (t1, r1, u1, v1), VHComp (t2, r2, u2, v2) -> (t1 == t2 || conv t1 t2) && (r1 == r2 || conv r1 r2) && (u1 == u2 || conv u1 u2) && (v1 == v2 || conv v1 v2)
    | VSub (a, i, u), VSub (b, j, v) -> (a == b || conv a b) && (i == j || conv i j) && (u == v || conv u v)
    | VOr _, _ | _, VOr _
    | VAnd _, _ | _, VAnd _
    | VNeg _, _ | _, VNeg _
    | VDir _, _ | _, VDir _ -> orEq v1 v2
    | VI, VI -> true
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
    | VNat, VNat | VZero, VZero -> true
    | VSucc u, VSucc v -> conv u v
    | VIndNat (c1, z1, s1), VIndNat (c2, z2, s2) -> conv c1 c2 && conv z1 z2 && conv s1 s2
    | VSup (a1, b1), VSup (a2, b2) -> conv a1 a2 && conv b1 b2
    | VIndW (a1, b1, c1), VIndW (a2, b2, c2) -> conv a1 a2 && conv b1 b2 && conv c1 c2
    | VIm u, VIm v -> conv u v
    | VInf u, VInf v -> conv u v
    | VJoin u, VJoin v -> conv u v
    | VIndIm (a1, b1), VIndIm (a2, b2) -> conv a1 a2 && conv b1 b2
    | VFla u, VFla v -> conv u v
    | VFlaCounit u, VFlaCounit v -> conv u v
    | VIndFla (a1, b1), VIndFla (a2, b2) -> conv a1 a2 && conv b1 b2
    | VCoequ (a1, b1, f1, g1), VCoequ (a2, b2, f2, g2) -> conv a1 a2 && conv b1 b2 && conv f1 f2 && conv g1 g2
    | VIota2 (a1, b1, f1, g1, c1), VIota2 (a2, b2, f2, g2, c2) -> conv a1 a2 && conv b1 b2 && conv f1 f2 && conv g1 g2 && conv c1 c2
    | VResp (a1, b1, f1, g1, c1), VResp (a2, b2, f2, g2, c2) -> conv a1 a2 && conv b1 b2 && conv f1 f2 && conv g1 g2 && conv c1 c2
    | VIndCoequ (a1, b1, f1, g1, x1, i1, p1), VIndCoequ (a2, b2, f2, g2, x2, i2, p2) ->
      (a1 == a2 || conv a1 a2) && (b1 == b2 || conv b1 b2) && (f1 == f2 || conv f1 f2) && (g1 == g2 || conv g1 g2) && (x1 == x2 || conv x1 x2) && (i1 == i2 || conv i1 i2) && (p1 == p2 || conv p1 p2)
    | VDisc (s1, a1), VDisc (s2, a2) -> (s1 == s2 || conv s1 s2) && (a1 == a2 || conv a1 a2)
    | VBase (s1, a1, x1), VBase (s2, a2, x2) -> (s1 == s2 || conv s1 s2) && (a1 == a2 || conv a1 a2) && (x1 == x2 || conv x1 x2)
    | VHub (s1, a1, f1), VHub (s2, a2, f2) -> (s1 == s2 || conv s1 s2) && (a1 == a2 || conv a1 a2) && (f1 == f2 || conv f1 f2)
    | VSpoke (s1, a1, f1, x1), VSpoke (s2, a2, f2, x2) -> (s1 == s2 || conv s1 s2) && (a1 == a2 || conv a1 a2) && (f1 == f2 || conv f1 f2) && (x1 == x2 || conv x1 x2)
    | VIndDisc (s1, a1, x1, nc1, nh1, ns1), VIndDisc (s2, a2, x2, nc2, nh2, ns2) ->
      (s1 == s2 || conv s1 s2) && (a1 == a2 || conv a1 a2) && (x1 == x2 || conv x1 x2) && (nc1 == nc2 || conv nc1 nc2) && (nh1 == nh2 || conv nh1 nh2) && (ns1 == ns2 || conv ns1 ns2)
    | VKan _, _ | _, VKan _ -> true
    | _, _ -> false
  end || convWithSystem (v1, v2) || convProofIrrel v1 v2

and convWithSystem = function
  | v, VApp (VSystem ts, _) | VApp (VSystem ts, _), v ->
    not (System.is_empty ts) && System.for_all (fun mu -> conv (upd mu v)) ts
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

and check ctx (e0 : exp) (t0 : value) = traceCheck e0 t0;
  try match e0, t0 with
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
  | EHole, v -> ignore (v, ctx)
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
    eqNf (getFormulaV ts) i;
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
    let (p, _, _) = match infer ctx f with
      | VKan _ -> (VLam (VI, (freshName "i", fun _ -> VKan Z.zero)), VKan Z.zero, VKan Z.zero)
      | v -> extPathP v in
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
               getFormulaV ts)
  | EGlue e -> ignore (extKan (infer ctx e)); inferGlue (eval ctx e)
  | EGlueElem (e, u0, a) -> check ctx e VI; let r = eval ctx e in let t = infer ctx a in
    check ctx u0 (partialv (equivPtSingl t) r); let u = eval ctx u0 in
    (* Γ, φ ⊢ a ≡ f t where u = [φ ↦ (T, (f, e), t)] *)
    List.iter (fun mu -> let v = app (upd mu u, VRef vone) in let f = vfst (vfst (vsnd v)) in
      eqNf (eval (faceEnv mu ctx) a) (app (f, vsnd (vsnd v)))) (solve r One);
    inferGlueElem r u t
  | EUnglue (r, u, e) -> let (t, r', u') = extGlue (infer ctx e) in
    eqNf (eval ctx r) r'; eqNf (eval ctx u) u'; t
  | EEmpty | EUnit | EBool | ENat -> VKan Z.zero
  | EStar -> VUnit | EFalse | ETrue -> VBool | EZero -> VNat
  | ESucc e -> check ctx e VNat; VNat
  | EIndEmpty e -> ignore (extSet (infer ctx e)); implv VEmpty (eval ctx e)
  | EIndUnit e -> inferInd false ctx VUnit e recUnit
  | EIndBool e -> inferInd false ctx VBool e recBool
  | EIndNat (c, z, s) ->
    let tc = eval ctx c in
    let (t1, (_, g)) = extPiG (infer ctx c) in
    eqNf t1 VNat;
    ignore (extSet (g (Var (freshName "n", VNat))));
    ignore (check ctx z (app (tc, VZero)));
    ignore (check ctx s (VPi (VNat, (freshName "n", fun n -> implv (app (tc, n)) (app (tc, VSucc n))))));
    VPi (VNat, (freshName "n", fun n -> app (tc, n)))
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
  | EFla e -> let t = infer ctx e in ignore (extSet t); t
  | EFlaUnit e -> VFla (infer ctx e)
  | EFlaCounit e -> extFla (infer ctx e)
  | EIndFla (a, b) -> ignore (extSet (infer ctx a)); let t = eval ctx a in
    let (c, (x, g)) = extPiG (infer ctx b) in eqNf (VFla t) c;
    ignore (extSet (g (Var (x, c)))); inferIndFla t (eval ctx b)
  | ECoequ (a, b, f, g) ->
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    let tb = eval ctx b in ignore (extSet (infer ctx b));
    check ctx f (implv ta tb); check ctx g (implv ta tb);
    VKan (extSet (infer ctx a))
  | EIota2 (a, b, f, g, c) ->
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    let tb = eval ctx b in ignore (extSet (infer ctx b));
    check ctx f (implv ta tb); check ctx g (implv ta tb);
    check ctx c tb; VCoequ (ta, tb, eval ctx f, eval ctx g)
  | EResp (a, b, f, g, c) ->
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    let tb = eval ctx b in ignore (extSet (infer ctx b));
    check ctx f (implv ta tb); check ctx g (implv ta tb);
    check ctx c ta;
    let ef = eval ctx f in let eg = eval ctx g in
    let ec = eval ctx c in let t = VCoequ (ta, tb, ef, eg) in
    let p = VPLam (VLam (VI, (freshName "i", fun _ -> t))) in
    VApp (VApp (VPathP p, VIota2 (ta, tb, ef, eg, app (ef, ec))), VIota2 (ta, tb, ef, eg, app (eg, ec)))
  | EIndCoequ (a, b, f, g, x, i, rho) ->
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    let tb = eval ctx b in ignore (extSet (infer ctx b));
    check ctx f (implv ta tb); check ctx g (implv ta tb);
    let ef = eval ctx f in let eg = eval ctx g in
    let t = VCoequ (ta, tb, ef, eg) in
    let tx = eval ctx x in
    check ctx x (implv t (VKan Z.zero));
    check ctx i (VPi (tb, (freshName "b", fun c -> app (tx, VIota2 (ta, tb, ef, eg, c)))));
    let ti = eval ctx i in
    check ctx rho (VPi (ta, (freshName "a", fun c ->
      let p = VPLam (VLam (VI, (freshName "k", fun k ->
        app (tx, appFormula (VResp (ta, tb, ef, eg, c)) k)))) in
      let u0 = app (ti, app (ef, c)) in let u1 = app (ti, app (eg, c)) in
      VApp (VApp (VPathP p, u0), u1))));
    VPi (t, (freshName "z", fun z -> app (tx, z)))
  | EDisc (s, a) ->
    let ts = eval ctx s in ignore (extSet (infer ctx s));
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    VKan (extSet (infer ctx a))
  | EBase (s, a, v) ->
    let ts = eval ctx s in ignore (extSet (infer ctx s));
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    check ctx v ta; VDisc (ts, ta)
  | EHub (s, a, f) ->
    let ts = eval ctx s in ignore (extSet (infer ctx s));
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    check ctx f (implv ts (VDisc (ts, ta))); VDisc (ts, ta)
  | ESpoke (s, a, f, y) ->
    let ts = eval ctx s in ignore (extSet (infer ctx s));
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    let ef = eval ctx f in let ey = eval ctx y in
    check ctx f (implv ts (VDisc (ts, ta)));
    check ctx y ts;
    let t = VDisc (ts, ta) in
    let p = VPLam (VLam (VI, (freshName "i", fun _ -> t))) in
    VApp (VApp (VPathP p, VHub (ts, ta, ef)), app (ef, ey))
  | EIndDisc (s, a, x, nc, nh, ns) ->
    let ts = eval ctx s in ignore (extSet (infer ctx s));
    let ta = eval ctx a in ignore (extSet (infer ctx a));
    let tx = eval ctx x in
    check ctx x (implv (VDisc (ts, ta)) (VKan Z.zero));
    check ctx nc (VPi (ta, (freshName "a", fun v -> app (tx, VBase (ts, ta, v)))));
    let tnc = eval ctx nc in
    check ctx nh (VPi (implv ts (VDisc (ts, ta)), (freshName "f", fun f ->
      VPi (VPi (ts, (freshName "s", fun v -> app (tx, app (f, v)))), (freshName "nF", fun _ ->
        app (tx, VHub (ts, ta, f)))))));
    let tnh = eval ctx nh in
    check ctx ns (VPi (implv ts (VDisc (ts, ta)), (freshName "f", fun f ->
      VPi (VPi (ts, (freshName "s", fun v -> app (tx, app (f, v)))), (freshName "nF", fun nF ->
        VPi (ts, (freshName "y", fun y ->
          let p = VPLam (VLam (VI, (freshName "k", fun k ->
            app (tx, appFormula (VSpoke (ts, ta, f, y)) k)))) in
          let u0 = app (app (tnh, f), nF) in
          let u1 = app (nF, y) in
          VApp (VApp (VPathP p, u0), u1))))))));
    VPi (VDisc (ts, ta), (freshName "z", fun z -> app (tx, z)))
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
