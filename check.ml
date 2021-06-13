open Ident
open Error
open Expr
open Eval

let traceHole v gma =
  print_string ("\nHole:\n\n" ^ Expr.showGamma gma ^ "\n" ^ String.make 80 '-' ^ "\n" ^ Expr.showValue v ^ "\n\n")

let traceCheck (e0 : exp) (t0 : value) : unit =
  if !Prefs.trace then (Printf.printf "CHECK: %s : %s\n" (showExp e0) (showValue t0); flush_all ()) else ()

let traceInfer (e0 : exp) : unit =
  if !Prefs.trace then (Printf.printf "INFER: %s\n" (showExp e0); flush_all ()) else ()

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u          -> raise (ExpectedPi u)

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (ExpectedSig u)

let isVSet : value -> bool = function
  | VKan _ -> true
  | VPre _ -> true
  | _      -> false

let isFibrant : value -> bool = function
  | VKan _ -> true
  | _      -> false

let imax a b = match a, b with
  | VKan u, VKan v -> VKan (max u v)
  | VPre u, VPre v -> VPre (max u v)
  | VPre u, VKan v -> VPre (max u v)
  | VKan u, VPre v -> VPre (max u v)
  | u, v -> ExpectedVSet (if isVSet u then v else u) |> raise

let implv a b rho = VPi (a, (No, b, rho))

let rec check env (e0 : exp) (t0 : value) = let (rho, gma) = env in
  traceCheck e0 t0; match e0, t0 with
  | ELam ((p, a), e), VPi (t, g) -> eqNf env (eval a env) t;
    let q = pat p in let gen = var q in
    let gma' = upLocal (upLocal gma p t) q t in
    check (upVar rho p gen, gma') e (closByVal gma g gen)
  | EPair (e1, e2), VSig (t, g) -> let _ = check env e1 t in
    check env e2 (closByVal gma g (eval e1 env))
  | EHole, v -> traceHole v gma
  | EAxiom (_, u), v -> eqNf env (eval u env) v
  | EPLam e, VNt (NApp (NApp (NPathP (VPLam g), u1), u2)) ->
    let v1 = app gma (eval e env, VNt NZero) in
    let v2 = app gma (eval e env, VNt NOne) in
    check env (rbV gma v1) (app gma (g, VNt NZero));
    check env (rbV gma v2) (app gma (g, VNt NOne));
    eqNf env v1 u1; eqNf env v2 u2
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
    let v1 = app gma (v, VNt NZero) in
    let v2 = app gma (v, VNt NOne) in
    let t1 = infer env (rbV gma v1) in
    let t2 = infer env (rbV gma v2) in
    begin match t1, t2 with
    | VKan u, VKan v ->
      if ieq u v then implv v1 (impl (rbV gma v2) (EKan u)) rho
      else raise (TypeIneq (VKan u, VKan v))
    | _, _ -> ExpectedFibrant (if isVSet t1 then t2 else t1) |> raise end
  | EAppFormula (f, x) ->
    check env x (VNt NI);
    begin match infer env f with
    | VNt (NApp (NApp (NPathP (VPLam g), u1), u2)) -> app gma (g, eval x env)
    | _ -> raise (ExpectedPath f) end
  | EI -> VPre 0 | EZero -> VNt NI | EOne -> VNt NI
  | ENeg e ->
    if infer env e = VNt NI
    then VNt NI else raise (InferError e0)
  | EOr (e1, e2) | EAnd (e1, e2) ->
    if infer env e1 = VNt NI && infer env e2 = VNt NI
    then VNt NI else raise (InferError e0)
  | e -> raise (InferError e)
