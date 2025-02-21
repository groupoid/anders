# Introduction

Type theory is a universal programming language of pure mathematics (for proving theorems),
which can contain an arbitrary number of consistent axioms, ordered in the form of
pseudo-isomorphisms: the functions encode (ways of constructing type elements) and
decode (dependent eliminators of the universal principle of type induction), and
their equations—beta and eta rules of computability and uniqueness. Usually, type
theory, as a programming language, already includes basic primitives (axioms in
the form of built-in types) and accompanying documentation explaining their application
in the form of lectures or summaries.

Adjunction triples provide a structural foundation for understanding the interaction
of dependent types in type theory. In the context of Martin-Löf Type Theory (MLTT),
the four fundamental type rules—formation, introduction, elimination, and
computation—correspond to different aspects of isomorphism within these
adjunctions. This perspective allows us to analyze the behavior of Π and Σ types systematically.

# Fibrational setting

In this framework, the Π type represents universally quantified dependent functions,
while the Σ type models dependent pairs. Their interpretations extend into various
branches of mathematics, each highlighting a distinct perspective on their structural role.
Below, we explore four such perspectives: categorical, set-theoretic, homotopical, and groupoidal.

## 1. Categorical Perspective: Π and Σ as Adjunctions (Kock-Wraith Interpretation)

From a categorical viewpoint, Π and Σ types arise naturally through adjunctions.
The key idea is that dependent function types correspond to right adjoints,
while dependent sum types correspond to left adjoints. This perspective,
pioneered by Kock-Wright, provides a logical foundation for interpreting
these types in categorical models of type theory.

* The adjunctions can be explicitly formulated as triples (Σf ⊢ f* ⊢ Πf):
  Given a fibration p: E → B, the Σ type corresponds to the left adjoint Σf,
  the base change functor f* is the middle functor, and the Π type corresponds
  to the right adjoint Πf.
* This aligns with the categorical interpretation of Π as an exponential
  object BA in a suitable category and Σ as a dependent coproduct.
  
## 2. Set-Theoretic Perspective: Σ and Constructive Axiom of Choice

In classical set theory, Σ types naturally model the totality of relations by
encoding dependent pairs (x, y) where y depends on x. This is crucial in
constructive mathematics, where the axiom of choice does not hold unrestrictedly.

## 3. Homotopical Perspective: Π Types as Fiber Bundles

In homotopy type theory, Π and Σ types correspond to fiberwise constructions in homotopy theory.
* Given a fibration p: E → B, the Σ type represents the total space E, while the Π type represents
  the space of sections Πx P(x), which generalizes function spaces in homotopy theory.
* The key homotopy-theoretic result is the isomorphism: Πx P(x) ≅ Hom(B, E)

# Identification setting

## 4. Groupoidal Perspective: Identity Systems and the Cubical Model

In the intensional theory of types, the type of equality is also built in as
type-theoretical primitives of the categorical meta-theoretical model of
conjugations of three Jacobs-Lawvere functors:

* Factor space (`Q`)
* Identification system (`=`)
* Contractible space (`C`)

These functors form another adjunction:

* (`Q` ⊢ `=` ⊢ `C`): The factor space functor Q is the left adjoint,
  the identification system `=` serves as the base functor,
  and the contractible space functor C is the right adjoint.

# Conclusion

The interplay between Π and Σ types across different mathematical disciplines showcases
their fundamental nature. Whether understood categorically as adjunctions, set-theoretically
as constructive choice principles, homotopically as fiber bundle structures, or groupoidally
as identity systems, these types form the backbone of constructive homotopy type theory.

The CCHM model strengthens these interpretations by ensuring computational validity,
making it a powerful foundation for both mathematical reasoning and formal verification
in proof assistants.
