Canonicity
==========

## Abstract

This document examines canonicity in the context of Anders, a theorem prover built
on a CCHM/CHM HST-based core, integrating cubical type theory (CCHM in CHM flavor)
with strict equality on pretypes. Canonicity ensures that every closed, well-typed
term in Anders reduces to a unique canonical form, such as true or false for booleans
or numerals like 0 or 1 for natural numbers. The text distinguishes normal forms—fully
evaluated terms—from canonical forms, noting that neutral terms (e.g., those with free
variables) do not achieve canonicity. For closed terms, this property is essential,
particularly within Anders’ intensional type system and its support for inductive
types. Challenges in proving canonicity arise in complex settings like cubical type
theory, potentially requiring additional axioms. In Anders, canonicity underpins
reliable computation and proof construction, aligning its theoretical foundations
with practical implementation.

## Intro

### Introduction to Canonicity

In programming languages and type theory, canonicity is the property that ensures every
well-typed term—a valid expression in a system—can be reduced to a unique, standard
representation called its canonical form. This idea is central to homotopy type theory (HoTT),
a framework that blends type theory with topological concepts. For example, in a system with
a boolean type, canonicity guarantees that any term of type Bool evaluates to either true or
false, not some ambiguous or intermediate value.

### Normal Forms and Evaluation

To grasp canonicity, we need to understand normal forms. A normal form is a term that
cannot be simplified further through computation. In HoTT, terms are reduced step-by-step
using evaluation rules. For instance, 1 + 2 might simplify to 3, its normal form. However,
not all normal forms are canonical. Neutral terms, such as x + 1 where x is an unknown
variable, remain unreduced because they depend on unresolved elements. Canonicity applies
specifically to closed terms—those without free variables—ensuring they reduce to a unique,
predictable value.

### The Canonicity Property in Practice

The canonicity property guarantees that any closed term of a specific type, like
a natural number (Nat), evaluates to a concrete numeral such as 0, 1, or 2, rather
than an arbitrary normal form. This is vital for both theoretical consistency and
practical programming. For example, it ensures that a function returning a Nat always
yields a definite number, making program outcomes reliable. In HoTT systems with inductive
types (e.g., natural numbers defined by constructors like zero and succ), proving
canonicity confirms that terms behave as intended.

### Challenges and Implications

In intensional type theories like HoTT, where equality between terms is strict,
canonicity ensures that closed terms have a single, standard representation.
However, in more complex systems—such as those with undecidable type checking
or advanced features like cubical type theory—establishing canonicity can be
difficult and may require additional computational rules or axioms. Despite
these challenges, canonicity remains a cornerstone of reliable computation.

## Coda

### 1.1 Syntactic Canonicity

Syntactic canonicity (sometimes referred to as computational canonicity)
states that every closed term of a certain type reduces to a canonical
form using the internal reduction rules of the type theory. Specifically,
for the type of natural numbers (Nat), syntactic canonicity means that
every closed term t : Nat reduces to a numeral n (i.e., `t ⇓ n` where `n ∈ ℕ`).

Formally: `Π (t: ℕ), Σ (n: ℕ), t ->* n`

### 1.2 Propositional canonicity

Propositional canonicity weakens syntactic canonicity by allowing
the equality between a closed term and a numeral to hold only up
to propositional equality `≡`, rather than requiring direct computational reduction.

Formally: `Π (t: ℕ), Σ (n: ℕ), t ≡ n`

This means that, while t may not reduce directly to n, there
exists a derivable equality proof `p : t ≡ n` in the type theory.

### 1.3 Homotopy Canonicity

Homotopy canonicity is even weaker. Instead of requiring a definitional
or propositional equality, it only guarantees that every closed term is
homotopically equivalent to a numeral. This is relevant in frameworks
like HoTT, where identity types may not be strictly computable but still
behave coherently up to homotopy.

Formally, in HoTT: `Π (t: ℕ), Σ (n: ℕ), Path ℕ t n`

### 1.4 Canonicity Across Type Theories

|Type Theory|Syntactical|Propositional|Homotopy                           |
|-----------|-----------|-------------|-----------------------------------|
|MLTT       |        Yes| Yes         | Yes                               |
|HoTT       |         No| Yes         | Yes (Bocquet, Kapulkin, Sattler)  |
|CCHM       |        Yes| Yes         | Yes (Coquand, Huber, Sattler)     |

Different type-theoretic frameworks impose different levels of canonicity.
While MLTT has full syntactic, propositional, and homotopy canonicity, HoTT
lacks syntactic canonicity but retains homotopy canonicity. Cubical HoTT
restores full canonicity using its explicit cubical structure. Understanding
these distinctions is crucial for developing computational and proof-theoretic
applications of type theory.

#### Failure of Syntactic Canonicity in HoTT

In Homotopy Type Theory, function extensionality and univalence introduce
higher-inductive types, making reduction ambiguous for closed terms.
Specifically, closed terms of Nat may contain elements that do not
normalize to a numeral but are still provably equal to one in homotopy.

#### Proof Idea for Propositional Canonicity in HoTT

Bocquet and Kapulkin-Sattler established that every term of Nat is
propositionally equal to a numeral. The idea is to use a strict Rezk
completion of the syntactic model to construct a fibrant replacement
where each closed term can be shown to be propositionally equal to a numeral.

#### Proof Idea for Homotopy Canonicity in Cubical Type Theory

Coquand, Huber, and Sattler proved homotopy canonicity using cubical models,
where paths (identity types) are explicitly represented as maps over the
interval type I. The crucial tool here is homogeneous composition (hcomp),
which ensures that any term in Nat is homotopically equivalent to a numeral,
enforcing canonicity in a structured manner.

Table 2: Mechanisms Ensuring Canonicity in Different Type Theories

| Type Theory | Mechanism for Canonicity                                              |
|-------------|-----------------------------------------------------------------------|
| MLTT        | Normalization via term reduction (syntactic canonicity)               |
| HoTT        | Homotopical fibrant replacement (propositional & homotopy canonicity) |
| CCHM        | Cubical paths + hcomp enforcing structured identity types             |

### 1.5 Example of Violating Syntactic Canonicity

`ℕ` defined in CCHM through `W`, `0`, `1`, `2` doesn't compute numerals expressions to same terms,
however they are propotionally canonical in CCHM though `hcomp`.

```
def ℕ-ctor := ind_2 (λ (f : 𝟐), U) 𝟎 𝟏
def ℕ := W (x : 𝟐), ℕ-ctor x
def zero : ℕ := sup 𝟐 ℕ-ctor 0₂ (ind₀ ℕ)
def succ (n : ℕ) : ℕ := sup 𝟐 ℕ-ctor 1₂ (λ (x : 𝟏), n)

def 𝟎⟶ℕ (C : ℕ → U) (f : 𝟎 → ℕ) : C zero → C (sup 𝟐 ℕ-ctor 0₂ f)
 := transp (<i> C (sup 𝟐 ℕ-ctor 0₂ (λ (x : 𝟎), ind₀ (PathP (<_> ℕ) (ind₀ ℕ x) (f x)) x @ i))) 0

def 𝟏⟶ℕ (C : ℕ → U) (f : 𝟏 → ℕ) : C (succ (f ★)) → C (sup 𝟐 ℕ-ctor 1₂ f)
 := transp (<i> C (sup 𝟐 ℕ-ctor 1₂ (λ (x : 𝟏), ind₁ (λ (y : 𝟏), PathP (<_> ℕ) (f ★) (f y)) (<_> f ★) x @ i))) 0

def ℕ-ind (C : ℕ → U) (z : C zero) (s : Π (n : ℕ), C n → C (succ n)) : Π (n : ℕ), C n
 := indᵂ 𝟐 ℕ-ctor C
    (ind₂ (λ (x : 𝟐), Π (f : ℕ-ctor x → ℕ), (Π (b : ℕ-ctor x), C (f b)) → C (sup 𝟐 ℕ-ctor x f))
          (λ (f : 𝟎 → ℕ) (g : Π (x : 𝟎), C (f x)), 𝟎⟶ℕ C f z)
          (λ (f : 𝟏 → ℕ) (g : Π (x : 𝟏), C (f x)), 𝟏⟶ℕ C f (s (f ★) (g ★))))
```

#### The Code

* `ℕ-ctor` is defined as a two-point inductive type,
  which is essentially the structure of natural numbers,
  with two constructors 0 (zero) and 1 (successor).

* The function `ℕ` defines the type of natural numbers
  by recursively applying the inductive constructor
  `ℕ-ctor` to `W` (a parameter that will allow for recursion).

* `zero` defines the natural number 0, and `succ` defines the successor function,
   producing the next natural number.

* The terms `𝟎⟶ℕ` and `𝟏⟶ℕ` define the transport functions for zero and successor cases,
  respectively, using transposition (transp).

#### Syntactic Canonicity

In the case of natural numbers through `W`, `0`, `1`, `2`, this would mean that terms involving
natural numbers reduce to either 0 or succ n for some n. In this case,
however, the terms seem to fail syntactic canonicity because of the way
they involve higher inductive types and path spaces.

* `PathP`: There is use of path types, which introduces potential non-canonical forms.
  For example, the `ind₀ (PathP (<_> ℕ) ...`) terms are path-dependent terms,
  where the result depends on the path between natural numbers. This creates
  a situation where the terms cannot necessarily be reduced directly to 0 or
  succ n since the path spaces themselves may involve complex terms.

* `W`: The definition of `ℕ` using `W` introduces a recursive structure.
  This is a higher inductive type, meaning that ℕ will involve non-canonical
  terms due to the nature of the recursion and the transport between
  different levels of the inductive structure.

#### Failures in Canonicity

* Non-normalizing terms: Because of the presence of path-dependent
  types `PathP` and recursive definitions involving higher inductive
  types like `W`, the terms may not always reduce to a simple form
  like 0 or succ n.

* Complexity in path spaces: The presence of path spaces (PathP)
  introduces a level of complexity where terms can fail to simplify
  to their normal form, especially if the path spaces themselves
  are complicated or not trivially reducible.

#### Reformulating Canonicity for Natural Numbers

To reformulate canonicity for natural numbers built using this approach, consider the following:

1) Explicit normal forms: Instead of using higher inductive types and path
   spaces directly in the constructors of `ℕ`, you could attempt to define
   explicit normal forms for each level of recursion. For example, if `ℕ`
   is constructed inductively, the recursion should be designed to
   ensure that each term reduces to a canonical form (either 0 or succ n).

2) Defining a simplification rule: You could introduce simplification rules
   for the terms involving `PathP` and `ind₂`. For example, if the term involves
   a path between two elements of the same type, it could simplify based on
   the structure of that path.

3) Weakening of transport functions: The use of transport
   functions (`𝟎⟶ℕ` and `𝟏⟶ℕ`) could be streamlined or simplified,
   possibly by ensuring that the terms they produce are more
   straightforward, avoiding the creation of complex path-dependent terms.

4) Avoiding path dependencies in constructors: If path dependencies
   are introduced in terms like `ℕ-ctor` x, ensuring they do not lead
   to terms that require higher reductions may help maintain
   syntactic canonicity. This might involve constructing the natural
   number terms without relying on path-dependent constructs, focusing
   on simpler inductive rules.

## Epilog

In summary, the failure of syntactic canonicity in the given example arises
due to the complexity introduced by path types, homotopy composition, and
the recursive definition via `W`. To reformulate it for canonicity, consider
reducing the reliance on path-dependent constructions and focusing on
explicit normal forms and simpler recursive definitions. Alternatively,
you could introduce simplification mechanisms for the terms involving
path spaces to ensure they normalize to canonical forms.

In the context of Constructive Cubical Higher Modalities (CCHM) and the
question of preserving syntactical canonicity when expressing natural
numbers `ℕ` using the type constructors `W`, `0`, `1`, and `2` (which are
typically used in higher inductive type theory), there are significant
challenges. However, understanding these challenges in detail can help
identify potential paths to express natural numbers while preserving
syntactical canonicity.

### Understanding the Problem with Syntactical Canonicity

In type theory, syntactical canonicity refers to the property that
every term of a given type has a unique, reduced form (also called "normal form").
This is important because it ensures that terms can be reduced deterministically
and without ambiguity, which is often a crucial feature of constructive type theories.

When natural numbers are expressed using higher inductive
types (like `W` in your example), path-dependent types and
the recursive constructions involving homotopy (e.g., `W`,
`PathP`, and `ind₂`) can introduce significant complexity. This
complexity can lead to the failure of syntactical canonicity, because:

Inductive structures involving path spaces (e.g., `PathP`) may not reduce
directly to canonical forms (like 0 or succ n) due to the presence of
higher-dimensional structures.

Recursion using `W` introduces non-trivial paths and depends on how the
recursion unfolds, which can result in terms that do not have simple normal forms.

Homotopy-theoretic aspects (like `hcomp`, `ind₂`) typically introduce more
flexibility in the way terms are constructed and reduced, which makes
maintaining syntactic canonicity more difficult.

### Can Nat in W, 0, 1, 2 Preserve Syntactical Canonicity in CCHM?

Expressing natural numbers `ℕ` using the approach via `W`, `0`, `1`, and `2` constructors
does not preserve syntactical canonicity in the standard
sense within CCHM. The introduction of higher inductive types, especially
the use of path-dependent terms, creates structures that do not always
reduce directly to canonical forms. More specifically, the failure of
canonicity is often a consequence of the following:

* Path spaces and homotopies: When `W` and path-dependent types are used,
  it introduces an extra layer of complexity, meaning terms in `ℕ` might
  reduce to non-normal forms, and paths between elements in `ℕ` can be non-trivial.

* Higher inductive types: The construction of `ℕ` via `W` leads to a
  structure that does not admit a simple reduction to 0 or succ n.
  The recursion over `W` induces terms that involve complex higher-dimensional
  paths, making it hard to guarantee that each term will have a canonical form.

### Is This a Dead End, or Can It Be Fixed?

It is a dead and and can be fixed!
There are established results in type theory, particularly in homotopy
type theory and constructive type theories, which show that the use of
higher inductive types can break syntactical canonicity. In fact, this
has been the subject of study, and there are theorems stating that higher
inductive types generally do not preserve syntactical canonicity.

However, this does not mean that expressing natural numbers via `W` and
path-dependent constructions is entirely unworkable. Instead, it means that:

* You may need to reconsider how you define your natural numbers
  and possibly avoid certain path-dependent constructions if you
  want to maintain syntactic canonicity.

* It might be possible to use simple inductive types or other definitions
  of `ℕ` that avoid the pitfalls of higher inductive types while still
  respecting constructive and homotopical principles.

* Direct inductive definition of `ℕ`: One way to preserve
  canonicity is to define by general induction or built-in.

## Conclusion

Canonicity links abstract type theory to concrete computational results.
By guaranteeing that terms reduce to unique, standard forms, it underpins
trustworthy programming languages and formal proofs. Rooted in HoTT, its
principles extend to broader system design, shaping how we reason about and build computational frameworks.

## Dedication

I describe this process as the three states of cognitive viscosity—syntactic,
propositional, and homotopical—each of which manifests across four levels of
depth: category theory, Grothendieck yoga, cohomology, and supergeometry.

Initially, within the framework of Martin-Löf Type Theory (MLTT), thinking
is rigid and constrained, resembling reinforced concrete. As one progresses
through the mandala (a metaphor for a structured path of thought or reasoning),
the experience of fibrational "breathing" (the dynamic, flexible interaction
of type structures) becomes apparent. This process involves immersion in
identification spaces (equivalence classes of types or structures, where
different representations are seen as equivalent). Over time, the calculus
of types and structures emerges, not merely within these identifications but
as an intrinsic feature of their structure. This reveals the presence of
computationally intractable gaps—holes in thought that cannot be computed,
referencing undecidable problems or phenomena that resist formalization or
computation within the system. The laws of normalization (reducing complex
terms to a simpler or canonical form) accelerate the complexity of patterns
to such a degree that the system approaches a state of homotopical viscosity,
where the reasoning becomes increasingly entangled and resistant to further simplification.

Ultimately, the final mode of reasoning eliminates all homotopical equalities (removing
redundancies between topologically equivalent structures) within the system of infinite
universes of two distinct types (a reference to type hierarchies and universe
polymorphism in type theory, where multiple "levels" of types exist).

A being that has eliminated all isomorphisms up to homotopical canonicity (removing
redundancies in the types and structures that preserve their topological or higher-order
identity) within the system of infinite universes (infinite hierarchies of types)
perceives reality as it truly is. This claim refers to the idea that, by resolving
all equivalences and redundancies in mathematical systems, one may approach the ultimate,
most refined understanding of the structures governing reality. "As it truly is" refers
to the idea of a reality whose structure is perfectly captured by these refined, canonical
mathematical models, unencumbered by the computational and cognitive limitations that
typically obscure such understanding.
