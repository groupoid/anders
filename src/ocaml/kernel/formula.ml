open Language.Prelude
open Language.Spec
open Term
open Rbv
open Gen

module Conjunction = Env
type conjunction = dir Conjunction.t

module Disjunction = Set.Make(struct
  type t = conjunction
  let compare = Conjunction.compare Dir.compare
end)
type disjunction = Disjunction.t

let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

let rec rawAnd (f, g) =
  match f, g with
  | VDir Zero, _ | _, VDir Zero -> VDir Zero
  | VDir One, f | f, VDir One   -> f
  | VAnd (f, g), h              -> VAnd (f, rawAnd (g, h))
  | f, g                        -> VAnd (f, g)

let rec rawOr (f, g) =
  match f, g with
  | VDir One, _  | _, VDir One  -> VDir One
  | VDir Zero, f | f, VDir Zero -> f
  | VOr (f, g), h               -> VOr (f, rawOr (g, h))
  | f, g                        -> VOr (f, g)

let singleton p x = Env.add p x Env.empty

let contrAtom : ident * dir -> value = function
  | (x, Zero) -> VNeg (Var (x, VI))
  | (x, One)  -> Var (x, VI)

let contrAnd (t : conjunction) : value =
  Conjunction.fold (fun k d acc -> rawAnd (contrAtom (k, d), acc)) t (VDir One)

let contrOr (t : disjunction) : value =
  Disjunction.fold (fun e e' -> rawOr (contrAnd e, e')) t (VDir Zero)

let meet = Env.union (fun _ x y -> if x = y then Some x else raise IncompatibleFaces)
let eps = Env.empty

let leq xs ys =
  Env.for_all (fun k d1 -> match Env.find_opt k ys with
    | Some d2 -> d1 = d2
    | None    -> false) xs

let lt xs ys = not (Env.equal (=) xs ys) && leq xs ys

let comparable xs ys = leq xs ys || leq ys xs

let rec andFormula (f, g) =
  let v = match f, g with
    | VDir Zero, _ | _, VDir Zero -> VDir Zero
    | VDir One, f  | f, VDir One  -> f
    | VAnd (f, g), h -> andFormula (f, andFormula (g, h))
    | VOr (f, g), h | h, VOr (f, g) ->
      orFormula (andFormula (f, h), andFormula (g, h))
    | f, g -> VAnd (f, g)
  in
  match v with
  | VAnd _ | VOr _ -> contrOr (uniq (extOr v))
  | _              -> v

and orFormula (f, g) =
  let v = match f, g with
    | VDir One, _  | _, VDir One  -> VDir One
    | VDir Zero, f | f, VDir Zero -> f
    | VOr (f, g), h -> orFormula (f, orFormula (g, h))
    | f, g -> VOr (f, g)
  in
  match v with
  | VOr _ -> contrOr (uniq (extOr v))
  | _     -> v

and negFormula : value -> value = function
  | VDir d      -> VDir (negDir d)
  | VNeg n      -> n
  | VAnd (f, g) -> orFormula (negFormula f, negFormula g)
  | VOr (f, g)  -> andFormula (negFormula f, negFormula g)
  | v           -> VNeg v

and extAnd : value -> conjunction = function
  | Var (x, _)        -> Conjunction.singleton x One
  | VNeg (Var (x, _)) -> Conjunction.singleton x Zero
  | VAnd (x, y)       -> meet (extAnd x) (extAnd y)
  | VDir One          -> Conjunction.empty
  | VDir Zero         -> raise IncompatibleFaces
  | v                 -> raise (Internal (ExpectedConj (rbV v)))

and extOr : value -> disjunction = function
  | VOr (x, y) -> Disjunction.union (extOr x) (extOr y)
  | VDir Zero  -> Disjunction.empty
  | VDir One   -> Disjunction.singleton Conjunction.empty
  | k          -> (try Disjunction.singleton (extAnd k) with IncompatibleFaces -> Disjunction.empty)

and uniq t =
  let super x y = not (Env.equal (=) x y) && leq y x in
  Disjunction.filter (fun x -> not (Disjunction.exists (super x) t)) t

let orEq f g =
  try Disjunction.equal (uniq (extOr f)) (uniq (extOr g))
  with Internal _ -> false

let andEq f g =
  try Env.equal (=) (extAnd f) (extAnd g)
  with Internal _ -> false

let nubRev xs =
  let ys = ref [] in
  List.iter (fun x ->
    if not (List.mem x !ys) then
      ys := x :: !ys) xs;
  !ys

let meets xs ys =
  let zs = ref [] in
  List.iter (fun x ->
    List.iter (fun y ->
      try zs := meet x y :: !zs
      with IncompatibleFaces -> ()) ys) xs;
  nubRev !zs

let meetss = List.fold_left meets [eps]

let union xs ys = nubRev (List.rev_append xs ys)

let forall i = System.filter (fun mu _ -> not (Env.mem i mu))

let mkSystem xs = System.of_seq (List.to_seq xs)
let unionSystem xs ys = System.union (fun _ e _ -> Some e) xs ys

let getFaceV xs = Env.fold (fun x d y -> andFormula (y, contrAtom (x, d))) xs vone
let getFormulaV ts = System.fold (fun x _ v -> orFormula (getFaceV x, v)) ts vzero

let reduceSystem ts x =
  match System.find_opt eps ts with
  | Some v -> v
  | None   -> VApp (VSystem ts, x)

let rec solve k x = match k, x with
  | VDir y, _ -> if x = y then [eps] else []
  | Var (p, _), _ -> [singleton p x]
  | VNeg n, _ -> solve n (negDir x)
  | VOr (f, g), One  | VAnd (f, g), Zero -> union (solve f x) (solve g x)
  | VOr (f, g), Zero | VAnd (f, g), One  -> meets (solve f x) (solve g x)
  | _, _ -> raise (Internal (DNFSolverError (rbV k, x)))

let bimap f g ts =
  let ts' =
    System.fold (fun mu t ->
      Env.bindings mu
      |> List.rev_map (fun (i, d) -> solve (f i) d)
      |> meetss
      |> List.rev_map (fun nu -> (nu, g nu t))
      |> List.rev_append) ts [] in

  (* ensure incomparability *)
  List.filter (fun (alpha, _) ->
    not (List.exists (fun (beta, _) -> lt beta alpha) ts')) ts'
  |> mkSystem

let keys ts = List.of_seq (Seq.map fst (System.to_seq ts))

let intersectionWith f =
  System.merge (fun _ x y ->
    match x, y with
    | Some a, Some b -> Some (f a b)
    | _,      _      -> None)
