open Expr

exception TypeMismatch of exp * value * value
exception InferError of exp
exception VariableNotFound of name
exception InvalidApplication of value * value
exception ExpectedPi of value
exception ExpectedSig of value

exception Core of string

let vfst : value -> value = function
  | VPair (u, _) -> u
  | VNt k        -> VNt (NFst k)
  | v            -> raise (ExpectedSig v)

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | VNt k        -> VNt (NSnd k)
  | v            -> raise (ExpectedSig v)

let rec lRho : rho -> int = function
  | Nil               -> 0
  | UpVar (rho, _, _) -> lRho rho + 1
  | UpDec (rho, _)    -> lRho rho

let rec lookup (x1 : name) (lst : gamma) =
  match lst with
  | (x2, v) :: xs -> if x1 = x2 then v else lookup x1 xs
  | []            -> raise (VariableNotFound x1)

let rec eval (e : exp) (rho : rho) =
  match e with
  | ESet -> VSet
  | EDec (d, e) -> eval e (UpDec (rho, d))
  | ELam (p, e) -> VLam (p, e, rho)
  | EPi (p, a, b) -> VPi (eval a rho, (p, b, rho))
  | ESig (p, a, b) -> VSig (eval a rho, (p, b, rho))
  | EFst e -> vfst (eval e rho)
  | ESnd e -> vsnd (eval e rho)
  | EApp (f, x) -> app (eval f rho, eval x rho)
  | EVar x -> getRho rho x
  | EPair (e1, e2) -> VPair (eval e1 rho, eval e2 rho)
and app : value * value -> value = function
  | (VLam f, v) -> closByVal f v
  | (VNt k, m)  -> VNt (NApp (k, m))
  | (x, y)      -> raise (InvalidApplication (x, y))
and closByVal (x : clos) (v : value) =
  match x with
  | (p, e, rho) -> eval e (UpVar (rho, p, v))
and getRho rho0 x =
  match rho0 with
  | Nil -> raise (VariableNotFound x)
  | UpVar (rho, p, v) ->
    if x = p then v
    else getRho rho x
  | UpDec (rho, (p, _, e)) ->
    if x = p then eval e rho0
    else getRho rho x

let pat (k : int) : name -> name = function
  | Hole        -> Hole
  | Name (p, _) -> Name (p, k)
let genV k n : value = VNt (NVar (pat k n))

let rec rbV (k : int) : value -> exp = function
  | VLam f         ->
    let (p, _, _) = f in
    ELam (pat k p, rbV (k + 1) (closByVal f (genV k p)))
  | VPair (u, v)   -> EPair (rbV k u, rbV k v)
  | VSet           -> ESet
  | VPi (t, g)     ->
    let (p, _, _) = g in
    EPi (pat k p, rbV k t, rbV (k + 1) (closByVal g (genV k p)))
  | VSig (t, g)    ->
    let (p, _, _) = g in
    ESig (pat k p, rbV k t, rbV (k + 1) (closByVal g (genV k p)))
  | VNt l          -> rbN k l
and rbN i : neut -> exp = function
  | NVar s              -> EVar s
  | NApp (k, m)         -> EApp (rbN i k, rbV i m)
  | NFst k              -> EFst (rbN i k)
  | NSnd k              -> ESnd (rbN i k)

let eqNf i e m1 m2 : unit =
  let e1 = rbV i m1 in
  let e2 = rbV i m2 in
  if e1 = e2 then ()
  else raise (TypeMismatch (e, m1, m2))

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u          -> raise (ExpectedPi u)

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (ExpectedSig u)

let rec each (f : 'a -> unit) : 'a list -> unit = function
  | [] -> ()
  | x :: xs -> f x; each f xs

let rec checkT k rho gma : exp -> unit = function
  | EPi (p, a, b) ->
    checkT k rho gma a;
    let gma1 = (p, eval a rho) :: gma in
    checkT (k + 1) (UpVar (rho, p, genV k p)) gma1 b
  | ESig (p, a, b) -> checkT k rho gma (EPi (p, a, b))
  | ESet -> ()
  | a -> let _ = check k rho gma a VSet in ()
and check k (rho : rho) (gma : gamma) (e0 : exp) (t0 : value) : rho * gamma =
  match e0, t0 with
  | ELam (p, e), VPi (t, g) ->
    let gen = genV k p in
    let gma1 = (p, t) :: gma in
    check (k + 1) (UpVar (rho, p, gen)) gma1 e (closByVal g gen)
  | EPair (e1, e2), VSig (t, g) ->
    let _ = check k rho gma e1 t in
    check k rho gma e2 (closByVal g (eval e1 rho))
  | ESet, VSet -> (rho, gma)
  | EPi (p, a, b), VSet ->
    let _ = check k rho gma a VSet in
    let gen = genV k p in
    let gma1 = (p, eval a rho) :: gma in
    check (k + 1) (UpVar (rho, p, gen)) gma1 b VSet
  | ESig (p, a, b), VSet ->
    check k rho gma (EPi (p, a, b)) VSet
  | EDec (d, e), t ->
    let (name, _, _) = d in
    Printf.printf "Checking: %s\n" (Expr.showName name);
    check k (UpDec (rho, d)) (snd (checkD k rho gma d)) e t
  | e, t -> eqNf k e t (checkI k rho gma e); (rho, gma)
and checkI k rho gma : exp -> value = function
  | EVar x -> lookup x gma
  | EApp (f, x) ->
    let t1 = checkI k rho gma f in
    let (t, g) = extPiG t1 in
    let _ = check k rho gma x t in
    closByVal g (eval x rho)
  | EFst e ->
    let t = checkI k rho gma e in fst (extSigG t)
  | ESnd e ->
    let t = checkI k rho gma e in
    let (_, g) = extSigG t in
    closByVal g (vfst (eval e rho))
  | e -> raise (InferError e)
and checkD k rho gma (d : decl) : rho * gamma =
  match d with
  | (p, a, e) ->
    checkT k rho gma a;
    let t = eval a rho in let gen = genV k p in
    let gma1 = (p, t) :: gma in
    check (k + 1) (UpVar (rho, p, gen)) gma1 e t

let checkMain filename rho gma e =
  Printf.printf "Parsed “%s” successfully.\n" filename;
  let rho = check 1 rho gma e VSet in
  Printf.printf "File loaded.\n"; rho

let prettyPrintError : exn -> unit = function
  | TypeMismatch (e, t, t0) ->
    Printf.printf "%s was expected to be\n  %s\nbut it is\n  %s\n"
      (Expr.showExp e) (Expr.showValue t) (Expr.showValue t0)
  | InferError e ->
    Printf.printf "Cannot infer type of\n  %s\n" (Expr.showExp e)
  | VariableNotFound p ->
    Printf.printf "Variable %s was not found\n" (Expr.showName p)
  | InvalidApplication (x, y) ->
    Printf.printf "Invalid application \n  %s\nto\n  %s\n"
                  (Expr.showValue x) (Expr.showValue y)
  | ExpectedPi x ->
    Printf.printf "  %s\nexpected to be Pi-type\n" (Expr.showValue x)
  | ExpectedSig x ->
    Printf.printf "  %s\nexpected to be Sigma-type\n" (Expr.showValue x)
  | ex -> Printf.printf "uncaught exception: %s" (Printexc.to_string ex)

let handleErrors (f : 'a -> 'b) (x : 'a) (default : 'b) : 'b =
  try f x with ex -> prettyPrintError ex; default

let checkAndEval rho gma (exp : exp) =
  let t = checkI 1 rho gma exp in
  let v = eval exp rho in
  Printf.printf "TYPE: %s\nEVAL: %s\n" (Expr.showValue t) (Expr.showValue v)

let rho : rho ref   = ref Nil
let gma : gamma ref = ref []
let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let filename = Sys.argv.(i) in let chan = open_in filename in
    let exp = Parser.exp Lexer.main (Lexing.from_channel chan) in
    close_in chan;
    let (rho1, gma1) =
      handleErrors (checkMain filename !rho !gma) exp
                   (!rho, !gma) in
    rho := rho1; gma := gma1
  done;
  while true do
    print_string "> ";
    let line = read_line () in
    let exp = Parser.repl Lexer.main (Lexing.from_string line) in
    handleErrors (checkAndEval !rho !gma) exp ()
  done