open Ident
open Error
open Expr

let mergeConj  xs = List.fold_left (fun e (_, e') -> EAnd (e', e)) (EDir One) xs
let getFormula xs = List.fold_left (fun e (x, _) -> EOr (mergeConj x, e)) (EDir Zero) xs

(* Arbitrary formula φ after calling andFormula/orFormula/negFormula
   will have form (α₁ ∧ ... ∧ αₙ) ∨ ... ∨ (β₁ ∧ ... ∧ βₘ),
   where “∧” and “∨” are right-associative,
   and each αᵢ/βⱼ has form “γ” or “−γ” for some variable “γ”. *)
let rec orFormula : value * value -> value = function
  | VDir One, _  | _, VDir One  -> VDir One
  | VDir Zero, f | f, VDir Zero -> f
  | VOr (f, g), h -> orFormula (f, orFormula (g, h))
  | f, g -> VOr (f, g)

let rec andFormula : value * value -> value = function
  | VDir Zero, _ | _, VDir Zero -> VDir Zero
  | VDir One, f  | f, VDir One  -> f
  | VAnd (f, g), h -> andFormula (f, andFormula (g, h))
  | VOr (f, g), h | h, VOr (f, g) ->
    orFormula (andFormula (f, h), andFormula (g, h))
  | f, g -> VAnd (f, g)

let rec negFormula : value -> value = function
  | VDir d      -> VDir (negDir d)
  | VNeg n      -> n
  | VAnd (f, g) -> orFormula (negFormula f, negFormula g)
  | VOr (f, g)  -> andFormula (negFormula f, negFormula g)
  | v           -> VNeg v

(* extAnd converts (α₁ ∧ ... ∧ αₙ) into set of names equipped with sign. *)
let rec extAnd : value -> conjunction = function
  | Var (x, _)        -> Conjunction.singleton (x, One)
  | VNeg (Var (x, _)) -> Conjunction.singleton (x, Zero)
  | VAnd (x, y)       -> Conjunction.union (extAnd x) (extAnd y)
  | VDir Zero         -> Conjunction.empty
  | v -> raise (ExpectedConjunction v)

(* extOr converts (α₁ ∧ ... ∧ αₙ) ∨ ... ∨ (β₁ ∧ ... ∧ βₘ)
   into list of extAnd results. *)
type disjunction = conjunction list
let rec extOr : value -> disjunction = function
  | VOr (x, y) -> List.rev_append (extOr x) (extOr y)
  | k          -> [extAnd k]

(* uniq removes all conjunctions that are superset of another,
   i. e. xy ∨ x = (x ∧ y) ∨ (x ∧ 1) = x ∧ (y ∨ 1) = x ∧ 1 = x.
   It does not remove conjunction like (x ∧ −x), because algebra of interval
   is not boolean, it is De Morgan algebra: distributive lattice with De Morgan laws.
   https://ncatlab.org/nlab/show/De+Morgan+algebra *)
let uniq f =
  let super x y = not (Conjunction.equal x y) && Conjunction.subset y x in
  List.filter (fun x -> not (List.exists (super x) f)) f

(* orSubset checks that all conjunctions from xs present in ys. *)
let orSubset xs ys =
  List.for_all (fun x -> List.exists (Conjunction.equal x) ys) xs

(* orEq checks equivalence of two formulas
   of the form (α₁ ∧ ... ∧ αₙ) ∨ ... ∨ (β₁ ∧ ... ∧ βₘ) *)
let orEq f g =
  let f' = uniq (extOr f) in let g' = uniq (extOr g) in
  orSubset f' g' && orSubset g' f'

(* andEq check equivalence of two formulas
   of the form (α₁ ∧ ... ∧ αₙ) *)
let andEq f g = Conjunction.equal (extAnd f) (extAnd g)

let meet phi psi : face =
  Env.merge (fun _ x y ->
    match x, y with
    | Some _, Some _ -> raise IncompatibleFaces
    | Some u, None   -> Some u
    | None,   Some v -> Some v
    | None,   None   -> None) phi psi

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

let union xs ys = nubRev (List.append xs ys)
let eps : face = Env.empty
let singleton p x = Env.add p x Env.empty
let faceEnv = Env.fold (fun p dir -> Env.add p (Local, Value VI, Value (VDir dir)))

let rec solve k x = match k, x with
  | VDir y, _ -> if x = y then [eps] else []
  | Var (p, _), _ -> [singleton p x]
  | VNeg n, _ -> solve n (negDir x)
  | VOr (f, g), One  | VAnd (f, g), Zero -> union (solve f x) (solve g x)
  | VOr (f, g), Zero | VAnd (f, g), One  -> meets (solve f x) (solve g x)
  | _, _ -> failwith (Printf.sprintf "Cannot solve: %s = %s" (showValue k) (showDir x))
