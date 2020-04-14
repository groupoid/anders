open Expr

exception NfEqError
exception Core of string

let vfst : value -> value = function
  | VPair (u, _) -> u
  | VNt k        -> VNt (NFst k)
  | _            -> raise (Core "vfst")

let vsnd : value -> value = function
  | VPair (_, u) -> u
  | VNt k        -> VNt (NSnd k)
  | _            -> raise (Core "vsnd")

let rec lRho : rho -> int = function
  | Nil               -> 0
  | UpVar (rho, _, _) -> lRho rho + 1
  | UpDec (rho, _)    -> lRho rho

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
  | (VNt k, m) -> VNt (NApp (k, m))
  | _ -> raise (Core "app")
and closByVal (x : clos) (v : value) =
  match x with
  | (p, e, rho) -> eval e (UpVar (rho, p, v))
and getRho rho0 x =
  match rho0 with
  | UpVar (rho, p, v) ->
    if x = p then v
    else getRho rho x
  | UpDec (rho, (p, _, e)) ->
    if x = p then eval e rho0
    else getRho rho x
  | _ -> raise (Core "getRho")

let rec lookup (s : name) (lst : gamma) =
  match lst with
  | x :: xs -> if s = fst x then snd x else lookup s xs
  | []      -> raise (Core ("lookup " ^ showName s))

let pat (k : int) : name -> name = function
  | Hole   -> Hole
  | Name p -> Name (p ^ string_of_int k)
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

let eqNf i m1 m2 : unit =
  let e1 = rbV i m1 in
  let e2 = rbV i m2 in
  if e1 = e2 then ()
  else raise NfEqError

let extPiG : value -> value * clos = function
  | VPi (t, g) -> (t, g)
  | u          -> raise (Core ("extPiG " ^ Expr.showValue u))

let extSigG : value -> value * clos = function
  | VSig (t, g) -> (t, g)
  | u           -> raise (Core ("extSigG " ^ Expr.showValue u))

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
  | a -> check k rho gma a VSet
and check k (rho : rho) (gma : gamma) (e0 : exp) (t0 : value) : unit =
  match e0, t0 with
  | ELam (p, e), VPi (t, g) ->
    let gen = genV k p in
    let gma1 = (p, t) :: gma in
    check (k + 1) (UpVar (rho, p, gen)) gma1 e (closByVal g gen)
  | EPair (e1, e2), VSig (t, g) ->
    check k rho gma e1 t;
    check k rho gma e2 (closByVal g (eval e1 rho))
  | ESet, VSet -> ()
  | EPi (p, a, b), VSet ->
    check k rho gma a VSet;
    let gen = genV k p in
    let gma1 = (p, eval a rho) :: gma in
    check (k + 1) (UpVar (rho, p, gen)) gma1 b VSet
  | ESig (p, a, b), VSet ->
    check k rho gma (EPi (p, a, b)) VSet
  | EDec (d, e), t ->
    let gma1 = checkD k rho gma d in
    check k (UpDec (rho, d)) gma1 e t
  | e, t ->
    let t0 = checkI k rho gma e in
    try eqNf k t t0
    with NfEqError ->
      Printf.printf "%s was expected to be\n  %s\nbut it is\n  %s\n"
        (Expr.showExp e) (Expr.showValue t) (Expr.showValue t0)
and checkI k rho gma : exp -> value = function
  | EVar x -> lookup x gma
  | EApp (f, x) ->
    let t1 = checkI k rho gma f in
    let (t, g) = extPiG t1 in
    check k rho gma x t;
    closByVal g (eval x rho)
  | EFst e ->
    let t = checkI k rho gma e in
    fst (extSigG t)
  | ESnd e ->
    let t = checkI k rho gma e in
    let (_, g) = extSigG t in
    closByVal g (vfst (eval e rho))
  | e -> raise (Core ("checkI: " ^ Expr.showExp e))
and checkD k rho gma (d : decl) : gamma =
  match d with
  | (p, a, e) ->
    checkT k rho gma a;
    let t = eval a rho in
    let gen = genV k p in
    let gma1 = (p, t) :: gma in
    check (k + 1) (UpVar (rho, p, gen)) gma1 e t;
    gma1

let checkMain e = check 0 Nil [] e VSet

let _ =
  for i = 1 to Array.length Sys.argv - 1 do
    let filename = Sys.argv.(i) in
    let chan = open_in filename in
    let text = really_input_string chan (in_channel_length chan) in
    close_in chan;
    let exp = Parser.exp Lexer.main (Lexing.from_string text) in
    Format.printf "Checking %s\n" filename;
    checkMain exp
  done