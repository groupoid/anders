open Language.Spec
open Term
open Rbv

module Atom =
struct
  type t = ident * dir
  let compare (a, x) (b, y) =
    if a = b then Dir.compare x y else Ident.compare a b
end

module Conjunction = Set.Make(Atom)
type conjunction = Conjunction.t

module Disjunction = Set.Make(Conjunction)
type disjunction = Disjunction.t

let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

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

(* extAnd converts (α₁ ∧ ... ∧ αₙ) into set of idents equipped with sign. *)
let rec extAnd : value -> conjunction = function
  | Var (x, _)        -> Conjunction.singleton (x, One)
  | VNeg (Var (x, _)) -> Conjunction.singleton (x, Zero)
  | VAnd (x, y)       -> Conjunction.union (extAnd x) (extAnd y)
  | v                 -> raise (Internal (ExpectedConj (rbV v)))

(* extOr converts (α₁ ∧ ... ∧ αₙ) ∨ ... ∨ (β₁ ∧ ... ∧ βₘ)
   into list of extAnd results. *)
let rec extOr : value -> disjunction = function
  | VOr (x, y) -> Disjunction.union (extOr x) (extOr y)
  | k          -> Disjunction.singleton (extAnd k)

(* uniq removes all conjunctions that are superset of another,
   i. e. xy ∨ x = (x ∧ y) ∨ (x ∧ 1) = x ∧ (y ∨ 1) = x ∧ 1 = x.
   It does not remove conjunction like (x ∧ −x), because algebra of interval
   is not boolean, it is De Morgan algebra: distributive lattice with De Morgan laws.
   https://ncatlab.org/nlab/show/De+Morgan+algebra *)
let uniq t =
  let super x y = not (Conjunction.equal x y) && Conjunction.subset y x in
  Disjunction.filter (fun x -> not (Disjunction.exists (super x) t)) t

(* orEq checks equivalence of two formulas
   of the form (α₁ ∧ ... ∧ αₙ) ∨ ... ∨ (β₁ ∧ ... ∧ βₘ) *)
let orEq f g = Disjunction.equal (uniq (extOr f)) (uniq (extOr g))

(* andEq check equivalence of two formulas
   of the form (α₁ ∧ ... ∧ αₙ) *)
let andEq f g = Conjunction.equal (extAnd f) (extAnd g)

let compatible xs ys =
  Env.merge (fun _ x y -> match x, y with
    | Some d1, Some d2 -> Some (d1 = d2)
    | _,       _       -> Some true) xs ys
  |> Env.for_all (fun _ b -> b)

let leq xs ys =
  Env.for_all (fun k d1 -> match Env.find_opt k ys with
    | Some d2 -> d1 = d2
    | None    -> false) xs

let lt xs ys = not (Env.equal (=) xs ys) && leq xs ys

let comparable xs ys = leq xs ys || leq ys xs

let meet = Env.union (fun _ x y -> if x = y then Some x else raise IncompatibleFaces)

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
let unionSystem xs ys = System.union (fun _ _ _ -> raise (Failure "unionSystem")) xs ys (* ??? *)

let sign x = function
  | Zero -> ENeg (EVar x)
  | One  -> EVar x

let getFace xs = Env.fold (fun x d y -> EAnd (y, sign x d)) xs (EDir One)
let getFormula ts = System.fold (fun x _ e -> EOr (getFace x, e)) ts (EDir Zero)

let singleton p x = Env.add p x Env.empty

let contrAtom : ident * dir -> value = function
  | (x, Zero) -> VNeg (Var (x, VI))
  | (x, One)  -> Var (x, VI)

let contrAnd (t : conjunction) : value =
  Conjunction.fold (fun e e' -> andFormula (contrAtom e, e')) t (VDir One)

let contrOr (t : disjunction) : value =
  Disjunction.fold (fun e e' -> orFormula (contrAnd e, e')) t (VDir Zero)

let getFaceV xs = Env.fold (fun x d y -> andFormula (y, contrAtom (x, d))) xs vone
let getFormulaV ts = System.fold (fun x _ v -> orFormula (getFaceV x, v)) ts vzero

let evalAnd a b =
  match andFormula (a, b) with
  | VAnd (a, b) -> contrAnd (extAnd (VAnd (a, b)))
  | v           -> v

let evalOr a b =
  match orFormula (a, b) with
  | VOr (a, b) -> contrOr (uniq (extOr (VOr (a, b))))
  | v          -> v

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
