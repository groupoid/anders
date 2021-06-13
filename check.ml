open Ident
open Error
open Expr
open Eval

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

let rec check (rho : rho) (gma : gamma) (e0 : exp) (t0 : value) = traceCheck e0 t0; match e0, t0 with
  | ELam ((p, a), e), VPi (t, g) -> eqNf (eval a rho) t; let gma' = upLocal gma p t in check (upVar rho p (genV p)) gma' e (closByVal g (genV p))
  | EPair (e1, e2), VSig (t, g) -> let _ = check rho gma e1 t in check rho gma e2 (closByVal g (eval e1 rho))
  | EHole, v -> print_string ("\nHole:\n\n" ^ Expr.showGamma gma ^ "\n" ^ String.make 80 '-' ^ "\n" ^ Expr.showValue v ^ "\n\n")
  | EAxiom (_, u), v -> eqNf (eval u rho) v
  | e, VPre u -> begin
    match infer rho gma e with
    | VKan v | VPre v -> if ieq u v then () else raise (TypeIneq (VPre u, VPre v))
    | t -> raise (TypeIneq (VPre u, t))
  end
  | e, t -> eqNf t (infer rho gma e)
and infer rho gma e0 : value = traceInfer e0; match e0 with
  | EVar x -> lookup x gma
  | EKan u -> VKan (u + 1)
  | EPi ((p, a), b) -> let v = infer (upVar rho p (genV p)) (upLocal gma p (eval a rho)) b in imax (infer rho gma a) v
  | ESig (x, y) -> infer rho gma (EPi (x, y))
  | EApp (f, x) -> let (t, g) = extPiG (infer rho gma f) in ignore (check rho gma x t); closByVal g (eval x rho)
  | EFst e -> fst (extSigG (infer rho gma e))
  | ESnd e -> let (_, g) = extSigG (infer rho gma e) in closByVal g (vfst (eval e rho))
  | EAxiom (_, e) -> eval e rho
  | EPre u -> VPre (u + 1)
  | EPathP (EPLam f) ->
    let v1 = app (eval f rho, VNt NZero) in
    let v2 = app (eval f rho, VNt NOne) in
    let t1 = infer rho gma (rbV v1) in
    let t2 = infer rho gma (rbV v2) in begin
    match t1, t2 with
    | VKan u, VKan v ->
      if ieq u v then VPi (v1, (No, impl (rbV v2) (EKan u), Env.empty))
      else raise (TypeIneq (VKan u, VKan v))
    | _, _ -> ExpectedFibrant (if isVSet t1 then t2 else t1) |> raise
  end
  | EI -> VPre 0
  | EZero -> VNt NI
  | EOne -> VNt NI
  | ENeg e ->
    if infer rho gma e = VNt NI
    then VNt NI else raise (InferError e0)
  | EOr (e1, e2) | EAnd (e1, e2) ->
    if infer rho gma e1 = VNt NI && infer rho gma e2 = VNt NI
    then VNt NI else raise (InferError e0)
  | e -> raise (InferError e)