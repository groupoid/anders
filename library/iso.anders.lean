{- Isomorphisms:
   - Unimorphism;
   - Minivalence.

   HoTT 2.4 Homotopies and equivalences

   Copyright (c) Groupoid Infinity, 2014-2022. -}

module iso where
import library/equiv

-- Post-Voevodsky CCHM/hcomp lemIso implementation

def fill0 (A B : U) (f : A -> B) (g : B -> A) (x0 x1 : A) (y : B) (p0 : Path B (f x0) y) (p1 : Path B (f x1) y) (t : Π (x : A), Path A (g (f x)) x) (i : I) : I -> A
 := hfill A (∂ i) (λ (k : I), [(i = 1) → t x0 @ k, (i = 0) → g y ]) (inc A (∂ i) (g (p0 @ -i)))

def fill1 (A B : U) (f : A -> B) (g : B -> A) (x0 x1 : A) (y : B) (p0 : Path B (f x0) y) (p1 : Path B (f x1) y) (t : Π (x : A), Path A (g (f x)) x) (i : I) : I -> A
 := hfill A (∂ i) (λ (k : I), [(i = 1) → t x1 @ k, (i = 0) → g y ]) (inc A (∂ i) (g (p1 @ -i)))

def fill2 (A B : U) (f : A -> B) (g : B -> A) (x0 x1 : A) (y : B) (p0 : Path B (f x0) y) (p1 : Path B (f x1) y) (t : Π (x : A), Path A (g (f x)) x) (i : I) : I -> A
 := hfill A (∂ i) (λ (k : I), [(i = 1) → fill1 A B f g x0 x1 y p0 p1 t k 1, (i = 0) → fill0 A B f g x0 x1 y p0 p1 t k 1]) (inc A (∂ i) (g y))

def sqA (A B : U) (f : A -> B) (g : B -> A) (x0 x1 : A) (y : B) (p0 : Path B (f x0) y) (p1 : Path B (f x1) y)
    (t : Π (x : A), Path A (g (f x)) x) (i j : I) : A
 := hcomp A (∂ i ∨ ∂ j) (λ (k : I), [(i = 1) → fill1 A B f g x0 x1 y p0 p1 t j -k,
                                     (i = 0) → fill0 A B f g x0 x1 y p0 p1 t j -k,
                                     (j = 1) → t (fill2 A B f g x0 x1 y p0 p1 t i 1) @ -k,
                                     (j = 0) → g y ]) (fill2 A B f g x0 x1 y p0 p1 t i j)

def sqB (A B : U) (f : A -> B) (g : B -> A) (x0 x1 : A) (y : B) (p0 : Path B (f x0) y) (p1 : Path B (f x1) y)
    (s : Π (y : B), Path B (f (g y)) y) (t : Π (x : A), Path A (g (f x)) x) (i j : I) : B
 := hcomp B (∂ i ∨ ∂ j) (λ (k : I), [(i = 1) → s (p1 @ -j) @ k,
                                     (i = 0) → s (p0 @ -j) @ k,
                                     (j = 1) → s (f ((<r> fill2 A B f g x0 x1 y p0 p1 t r 1) @ i)) @ k,
                                     (j = 0) → s y @ k ]) (f (sqA A B f g x0 x1 y p0 p1 t i j))

def lemIso (A B : U) (f : A -> B) (g : B -> A) (s : Π (y : B), Path B (f (g y)) y) (t : Π (x : A), Path A (g (f x)) x)
    (x0 x1 : A) (y : B) (p0 : Path B y (f x0)) (p1 : Path B y (f x1)) : Path (fiber A B f y) (x0, p0) (x1, p1)
 := <i> ((<r> fill2 A B f g x0 x1 y (<k> p0 @ -k) (<k> p1 @ -k) t r 1) @ i, <j> sqB A B f g x0 x1 y (<k> p0 @ -k) (<k> p1 @ -k) s t i j)

-- [Shulman, Lumsdaine, Warren, Licata] 2010

def isoToEquiv (A B : U) (f : A -> B) (g : B -> A) (s : Π (y : B), Path B (f (g y)) y) (t : Π (x : A), Path A (g (f x)) x)
  : isEquiv A B f := \ (y : B), ((g y,<i> s y @ -i), \ (z : fiber A B f y), lemIso A B f g s t (g y) z.1 y (<i> s y @ -i) z.2)

-- [Cohen, Coquand, Huber, Mörtberg] 2016

def iso (A B: U) : U := Σ (f : A -> B) (g : B -> A) (s : section A B f g) (t : retract A B f g), unit

def isoPath (A B : U)
    (f : A -> B) (g : B -> A)
    (s : Π (y : B), Path B (f (g y)) y)
    (t : Π (x : A), Path A (g (f x)) x)
  : PathP (<_> U) A B
 := <i> Glue B (∂ i) [(i = 0) -> (A, f, isoToEquiv A B f g s t),
                      (i = 1) -> (B, id B, idIsEquiv B)]

-- Similar to Fibrational Equivalence the notion of Retract/Section based Isomorphism could be introduced
-- as forth-back transport between isomorphism and path equality. This notion is somehow cannonical to all
-- cubical systems and is called Unimorphism here.

-- Unimorphism Type (Iso -> Path)

def iso-Form (A B: U) : U₁ := iso A B -> PathP (<_>U) A B
def iso-Intro (A B: U) : iso-Form A B := \ (x : iso A B), isoPath A B x.f x.g x.s x.t
def iso-Elim (A B : U) : PathP (<_> U) A B -> iso A B
 := λ (p : PathP (<_> U) A B), ( coerce A B p, coerce B A (<i> p @ -i), trans⁻¹-trans A B p, λ (a : A), <k> trans-trans⁻¹ A B p a @ -k, star )

-- The notion of Minivalence as forth-back map between fibrational equivalence
-- and section/retract-based isomorphism is mentioned in Cubical Agda sources.

-- Minivalence Type (Iso -> Equiv)

def mini-Form (A B : U) : U := iso A B -> equiv A B
def mini-Intro (A B : U) : mini-Form A B := \ (x : iso A B), univ-elim A B (isoPath A B x.f x.g x.s x.t)
def mini-Elim (A B : U) : equiv A B -> iso A B := \ (x : equiv A B), ( x.f, inv-equiv A B x, ret-equiv A B x, sec-equiv A B x, star)

-- The other notion of equality such as Half Adjoint Equivalence and
-- Bi-Invertible Equivalences could be introduced and encoded as isomorphism by analogy.

def isHae (A B : U) (f : A -> B): U :=
  Σ (g : B -> A) (eta_: Path (idᵀ A) (∘ A B A g f) (id A)) (eps_: Path (idᵀ B) (∘ B A B f g) (id B)),
  Π (x : A), Path B (f ((eta_ @ 0) x)) ((eps_ @ 0) (f x))

def hae (A B : U) : U := Σ (f : A -> B), isHae A B f
