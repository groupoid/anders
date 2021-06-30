open Ident
open Error
open Expr

let rec orNeut : neut * neut -> neut = function
  | NDir One, _  | _, NDir One  -> NDir One
  | NDir Zero, f | f, NDir Zero -> f
  | NOr (f, g), h -> orNeut (f, orNeut (g, h))
  | f, g -> NOr (f, g)

let rec andNeut : neut * neut -> neut = function
  | NDir Zero, _ | _, NDir Zero -> NDir Zero
  | NDir One, f  | f, NDir One  -> f
  | NAnd (f, g), h -> andNeut (f, andNeut (g, h))
  | NOr (f, g), h | h, NOr (f, g) ->
    orNeut (andNeut (f, h), andNeut (g, h))
  | f, g -> NAnd (f, g)

let negDir : dir -> dir = function
  | Zero -> One | One -> Zero

let rec negNeut : neut -> neut = function
  | NDir d      -> NDir (negDir d)
  | NVar p      -> NNeg (NVar p)
  | NNeg n      -> n
  | NAnd (f, g) -> orNeut (negNeut f, negNeut g)
  | NOr (f, g)  -> andNeut (negNeut f, negNeut g)
  | k           -> raise (InvalidFormulaNeg (VNt k))

(* Arbitrary formula φ after calling andFormula/orFormula/negFormula
   will have form (α₁ ∧ ... ∧ αₙ) ∨ ... ∨ (β₁ ∧ ... ∧ βₘ),
   where “∧” and “∨” are right-associative,
   and each αᵢ/βⱼ has form “γ” or “−γ” for some variable “γ”. *)
let andFormula a b = match a, b with
  | VNt u, VNt v -> VNt (andNeut (u, v))
  | _, _         -> raise (InvalidFormulaAnd (a, b))

let orFormula a b = match a, b with
  | VNt u, VNt v -> VNt (orNeut (u, v))
  | _, _         -> raise (InvalidFormulaOr (a, b))

let negFormula a = match a with
  | VNt u -> VNt (negNeut u)
  | _     -> raise (InvalidFormulaNeg a)

module Dir = struct
  type t = dir
  let compare a b =
    match a, b with
    | One, Zero -> 1
    | Zero, One -> -1
    | _, _      -> 0
end

module Atom = struct
  type t = name * dir
  let compare (a, x) (b, y) =
    if a = b then Dir.compare x y else Name.compare a b
end

module Conjunction = Set.Make(Atom)
type conjunction = Conjunction.t

(* extAnd converts (α₁ ∧ ... ∧ αₙ) into set of names equipped with sign. *)
let rec extAnd : neut -> conjunction = function
  | NVar x               -> Conjunction.singleton (x, One)
  | NNeg (NVar x)        -> Conjunction.singleton (x, Zero)
  | NAxiom (x, _)        -> Conjunction.singleton (name x, One)
  | NNeg (NAxiom (x, _)) -> Conjunction.singleton (name x, Zero)
  | NAnd (x, y)          -> Conjunction.union (extAnd x) (extAnd y)
  | k -> failwith (Printf.sprintf "“%s” expected to be conjunction (should never happen)" (showNeut k))

(* extOr converts (α₁ ∧ ... ∧ αₙ) ∨ ... ∨ (β₁ ∧ ... ∧ βₘ)
   into list of extAnd results. *)
type disjunction = conjunction list
let rec extOr : neut -> disjunction = function
  | NOr (x, y) -> List.rev_append (extOr x) (extOr y)
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

module Face = Map.Make(Name)
type face = dir Face.t

let meet phi psi : face =
  Face.merge (fun k x y ->
    match x, y with
    | Some u, Some v -> raise IncompatibleFaces
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
let eps : face = Face.empty
let singleton p x = Face.add p x Face.empty
let faceEnv = Face.fold (fun p dir -> Env.add p (Local, VNt NI, Value (VNt (NDir dir))))

let rec solve k x = match k, x with
  | NDir y, _ -> if x = y then [eps] else []
  | NVar p, _ -> [singleton p x]
  | NNeg n, _ -> solve n (negDir x)
  | NOr (f, g), One  | NAnd (f, g), Zero -> union (solve f x) (solve g x)
  | NOr (f, g), Zero | NAnd (f, g), One  -> meets (solve f x) (solve g x)
  | _, _ -> failwith (Printf.sprintf "Cannot solve: %s = %s" (showNeut k) (showDir x))
