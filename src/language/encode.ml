open Prelude
open Spec

module type Writer =
sig
  val put  : char -> unit
  val puts : string -> unit
end

module Encode (W : Writer) =
struct
  (* I think there should be more efficient way to do this *)
  let int64 n =
    for i = 0 to 7 do
      Int64.shift_right n (i * 8)
      |> Int64.logand 255L
      |> Int64.to_int
      |> Char.chr
      |> W.put
    done

  let int = Int64.of_int >> int64
  let string xs = int (String.length xs); W.puts xs
  let integer = Z.to_bits >> string

  let ident = function
    | Irrefutable -> W.put '\x00'
    | Ident (xs, n) -> W.put '\xFF'; string xs; int64 n

  let dir = function
    | Zero -> W.put '\x00'
    | One  -> W.put '\xFF'

  let face mu = int (Env.cardinal mu);
    Env.iter (fun i d -> ident i; dir d) mu

  let rec exp = function
    | EHole                -> W.put '\x01'
    | EPre n               -> W.put '\x02'; integer n
    | EKan n               -> W.put '\x03'; integer n
    | EVar x               -> W.put '\x04'; ident x
    | EPi (a, (p, b))      -> clos '\x10' a p b
    | ELam (a, (p, b))     -> clos '\x11' a p b
    | EApp (f, x)          -> W.put '\x12'; exp2 f x
    | ESig (a, (p, b))     -> clos '\x13' a p b
    | EPair (_, a, b)      -> W.put '\x14'; exp2 a b
    | EFst e               -> W.put '\x15'; exp e
    | ESnd e               -> W.put '\x16'; exp e
    | EField (e, x)        -> W.put '\x17'; exp e; string x
    | EId e                -> W.put '\x20'; exp e
    | ERef e               -> W.put '\x21'; exp e
    | EJ e                 -> W.put '\x22'; exp e
    | EPathP e             -> W.put '\x23'; exp e
    | EPLam e              -> W.put '\x24'; exp e
    | EAppFormula (p, i)   -> W.put '\x25'; exp2 p i
    | EI                   -> W.put '\x26'
    | EDir Zero            -> W.put '\x27'
    | EDir One             -> W.put '\x28'
    | EAnd (i, j)          -> W.put '\x29'; exp2 i j
    | EOr (i, j)           -> W.put '\x2A'; exp2 i j
    | ENeg e               -> W.put '\x2B'; exp e
    | ETransp (p, i)       -> W.put '\x30'; exp2 p i
    | EHComp (t, r, u, u0) -> W.put '\x31'; exp4 t r u u0
    | EPartial e           -> W.put '\x32'; exp e
    | EPartialP (u, r)     -> W.put '\x33'; exp2 u r
    | ESystem ts           -> W.put '\x34'; system ts
    | ESub (a, i, u)       -> W.put '\x35'; exp3 a i u
    | EInc (t, r)          -> W.put '\x36'; exp2 t r
    | EOuc e               -> W.put '\x37'; exp e
    | EGlue t              -> W.put '\x38'; exp t
    | EGlueElem (r, u, a)  -> W.put '\x39'; exp3 r u a
    | EUnglue (r, u, e)    -> W.put '\x3A'; exp3 r u e
    | EEmpty               -> W.put '\x40'
    | EIndEmpty t          -> W.put '\x41'; exp t
    | EUnit                -> W.put '\x42'
    | EStar                -> W.put '\x43'
    | EIndUnit t           -> W.put '\x44'; exp t
    | EBool                -> W.put '\x45'
    | EFalse               -> W.put '\x46'
    | ETrue                -> W.put '\x47'
    | EIndBool t           -> W.put '\x48'; exp t
    | EW (a, (p, b))       -> clos '\x49' a p b
    | ESup (a, b)          -> W.put '\x4A'; exp2 a b
    | EIndW (a, b, c)      -> W.put '\x4B'; exp3 a b c
    | EIm t                -> W.put '\x50'; exp t
    | EInf e               -> W.put '\x51'; exp e
    | EIndIm (t, f)        -> W.put '\x52'; exp2 t f
    | EJoin e              -> W.put '\x53'; exp e

  and exp2 a b = exp a; exp b
  and exp3 a b c = exp a; exp b; exp c
  and exp4 a b c d = exp a; exp b; exp c; exp d

  and clos idx a p b = W.put idx; exp a; ident p; exp b

  and system ts = int (System.cardinal ts);
    System.iter (fun mu e -> face mu; exp e) ts

  let req = function
    | Check (e, t)     -> W.put '\x10'; exp e; exp t
    | Infer e          -> W.put '\x11'; exp e
    | Eval e           -> W.put '\x12'; exp e
    | Conv (e1, e2)    -> W.put '\x13'; exp2 e1 e2
    | Def (x, t, e)    -> W.put '\x20'; string x; exp2 t e
    | Assign (x, t, e) -> W.put '\x21'; string x; exp2 t e
    | Assume (x, t)    -> W.put '\x22'; string x; exp t
    | Erase x          -> W.put '\x23'; string x
    | Wipe             -> W.put '\x24'
    | Set (p, x)       -> W.put '\x30'; string p; string x
    | Version          -> W.put '\x31'
    | Ping             -> W.put '\x32'

  let rec error = function
    | Unknown x              -> W.put '\x01'; string x
    | Ineq (e1, e2)          -> W.put '\x02'; exp2 e1 e2
    | ExpectedPi e           -> W.put '\x03'; exp e
    | ExpectedSig e          -> W.put '\x04'; exp e
    | ExpectedType e         -> W.put '\x05'; exp e
    | ExpectedKan e          -> W.put '\x06'; exp e
    | ExpectedPath e         -> W.put '\x07'; exp e
    | ExpectedSubtype e      -> W.put '\x08'; exp e
    | ExpectedSystem e       -> W.put '\x09'; exp e
    | ExpectedConj e         -> W.put '\x0A'; exp e
    | ExpectedIm e           -> W.put '\x0B'; exp e
    | ExpectedInf e          -> W.put '\x0C'; exp e
    | ExpectedGlue e         -> W.put '\x0D'; exp e
    | ExpectedSup e          -> W.put '\x0E'; exp e
    | DNFSolverError (e, d)  -> W.put '\x0F'; exp e; dir d
    | AlreadyDeclared x      -> W.put '\x10'; string x
    | VariableNotFound x     -> W.put '\x11'; ident x
    | InferError e           -> W.put '\x12'; exp e
    | Traceback (e, es)      -> W.put '\x13'; error e; int (List.length es); List.iter (uncurry exp2) es
    | InvalidOpt p           -> W.put '\x14'; string p
    | InvalidOptValue (p, x) -> W.put '\x15'; string p; string x

  let resp = function
    | Version (i, j, k) -> W.put '\x10'; int64 i; int64 j; int64 k
    | Trace (x, es)     -> W.put '\x11'; string x; int (List.length es); List.iter exp es
    | Hole (e, gma)     -> W.put '\x12'; exp e; int (List.length gma); List.iter (fun (i, e) -> ident i; exp e) gma
    | Error err         -> W.put '\x13'; error err
    | Bool false        -> W.put '\x20'
    | Bool true         -> W.put '\x21'
    | Term e            -> W.put '\x22'; exp e
    | Pong              -> W.put '\xF0'
    | OK                -> W.put '\x00'
end

module Serialize = Encode(struct
  let put  = print_char
  let puts = print_string
end)