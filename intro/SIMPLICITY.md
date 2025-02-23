# Dan Kan: Simplicial HoTT

Groupoid Infinity Simplicial HoTT pure algebraїc implementation with explicit syntaxt for fastest type checking.
It supports following extensions: `Chain`, `Simplex`, `Simplicial`, `Category`, `Monoid`, `Group`.
Simplicial HoTT is a Rezk/GAP replacement incorporated into CCHM/CHM/HTS Agda-like Anders/Dan core.

<img src="https://dan.groupoid.space/styles/Daniel_Kan.JPG"></img>

## Abstract

We present a domain-specific language (DSL) extension to Cubical Homotopy Type Theory (CCHM) for simplicial structures,
designed as a fast type checker with a focus on algebraic purity. Built on the Cohen-Coquand-Huber-Mörtberg (CCHM)
framework, our DSL employs a Lean/Anders-like sequent syntax `П (context) ⊢ k (v₀, ..., vₖ | f₀, ..., fₗ | ... )` to define 
k-dimensional `0, ..., n, ∞` simplices via explicit contexts, vertex lists, and face relations, eschewing geometric coherence terms
in favor of compositional constraints (e.g., `f = g ∘ h`). The semantics, formalized as inference rules in a Martin-Löf
Type Theory MLTT-like setting, include Formation, Introduction, Elimination, Composition, Computational, and
Uniqueness rules, ensuring a lightweight, deterministic computational model with linear-time type checking (O(k + m + n),
where k is vertices, m is faces, and n is relations). Inspired by opetopic purity, our system avoids cubical
path-filling (e.g., `PathP`), aligning with syntactic approaches to higher structures while retaining CCHM’s
type-theoretic foundation. Compared to opetopic sequent calculi and the Rzk prover, our DSL balances algebraic
simplicity with practical efficiency, targeting simplicial constructions over general ∞-categories,
and achieves a fast, pure checker suitable for formal proofs and combinatorial reasoning.

## Compile and Run

```
$ ocamlopt -o dan src/simplicity.ml && ./dan
```

## Syntax

Incorporating into CCHM/CHM/HTS Anders/Dan core.

### Definition

New sequent contruction:

```
def <name> : <type> := П (context), conditions ⊢ <n> (elements | constraints)
```

Instances:

```
def chain : Chain := П (context), conditions ⊢ n (C₀, C₁, ..., Cₙ | ∂₀, ∂₁, ..., ∂ₙ₋₁)
def simplicial : Simplicial := П (context), conditions ⊢ n (s₀, s₁, ..., sₙ | facemaps, degeneracies)
def group : Group := П (context), conditions ⊢ n (generators | relations)
def cat : Category := П (context), conditions ⊢ n (objects | morphisms | coherence)
```

### BNF

```
<program> ::= <definition> | <definition> <program>
<definition> ::= "def" <id> ":" <type-name> ":=" <type-term>
<type-name> ::= "Simplex" | "Group" | "Simplicial" | "Chain" | "Cochain" | "Category" | "Monoid"
<type-term> ::= "П" "(" <context> ")" "⊢" <n> "(" <elements> "|" <constraints> ")" 
<digit> ::= "0" | "1" | "2" | "3" | "4" | "5" | "6" | "7" | "8" | "9"
<superscript> ::= "¹" | "²" | "³" | "⁴" | "⁵" | "⁶" | "⁷" | "⁸" | "⁹"
<n> ::= <digit> | <digit> <n> | "∞"
<context> ::= <hypothesis> | <hypothesis> "," <context>
<hypothesis> ::= <id> ":" <type-term>               % Single declaration, e.g., a : Simplex
               | "(" <id-list> ":" <type-term> ")"  % Grouped declaration, e.g., (a b c : Simplex)
               | <id> "=" <t> "<" <t>               % Map, e.g., ∂₁ = C₂ < C₃
               | <id> "=" <t> "∘" <t>               % Equality, e.g., ac = ab ∘ bc
<id-list> ::= <id> | <id> <id-list>                 % e.g., a b c
<elements> ::= <element-list> | ε 
<element-list> ::= <id> | <id> "," <element-list>
<constraints> ::= <constraint-list> | ε
<constraint-list> ::= <constraint> | <constraint>  "," <constraint-list>
<constraint> ::= <t> "=" <t>                        % Equality (e.g., a ∘ a = e)
               | <id> "<" <id>                      % Map (e.g., ∂₁ < C₂)
<t> ::= <id>                                        % e.g., a
      | <t> "∘" <t>                                 % e.g., a ∘ b
      | <t> "^-1"                                   % e.g., a^-1
      | <t> "^" <superscript>                       % e.g., a³
      | "e"                                         % identity
```

Meaning of `<n>` Across Types:

* Simplex: Dimension of the simplex—e.g., n=2 for a triangle (2-simplex).
* Group: Number of generators—e.g., n=1 for Z/3Z (one generator a).
* Simplicial: Maximum dimension of the simplicial set—e.g., n=1 for S1 (up to 1-simplices).
* Chain: Length of the chain (number of levels minus 1)—e.g., n=2 for a triangle chain (0, 1, 2 levels).
* Category: Number of objects—e.g., n=2 for a path category (two objects x,y).
* Monoid: Number of generators—e.g., n=2 for N (zero and successor).

## Semantics

### Chain

1. Formation. Γ ⊢ Chain : Set
2. Intro. Γ ⊢ n (S | R) : Chain  if  Γ = s₀₁, …, sₙₘₙ : Simplex, r₁, …, rₚ ∧ S₀, S₁, …, Sₙ = (s₀₁, …, s₀ₘ₀), …, (sₙ₁, …, sₙₘₙ) ∧ ∀ rⱼ = tⱼ = tⱼ', Γ ⊢ rⱼ : tⱼ = tⱼ' ∧ ∀ ∂ᵢⱼ < sₖₗ, Γ ⊢ ∂ᵢⱼ : sₖₗ → sₖ₋₁,ₘ
3. Elim Face. Γ ⊢ ∂ᵢⱼ s : Simplex  if  Γ ⊢ n (S | R) : Chain ∧ r = ∂ᵢⱼ < s ∧ r ∈ R ∧ s ∈ S
4. Comp Face. ∂ᵢⱼ (n (S | R)) → s'  if  r = ∂ᵢⱼ < s' ∧ r ∈ R ∧ s' ∈ S
5. Uniq Face. Γ ⊢ ∂ᵢⱼ s ≡ ∂ᵢⱼ s'  if  Γ ⊢ n (S | R) : Chain ∧ n (S' | R') : Chain ∧ s ∈ S ∧ s' ∈ S' ∧ ∀ r = ∂ᵢⱼ < s ∈ R ∧ r' = ∂ᵢⱼ < s' ∈ R'

### Cochain

1. Formation. Γ ⊢ Cochain : Set
2. Intro. Γ ⊢ n (S | R) : Cochain  if  Γ = s₀₁, …, sₙₘₙ : Simplex, r₁, …, rₚ ∧ S₀, S₁, …, Sₙ = (s₀₁, …, s₀ₘ₀), …, (sₙ₁, …, sₙₘₙ) ∧ ∀ rⱼ = tⱼ = tⱼ', Γ ⊢ rⱼ : tⱼ = tⱼ' ∧ ∀ σᵢⱼ < sₖₗ, Γ ⊢ σᵢⱼ : sₖₗ → sₖ₊₁,ₘ
3. Elim Degeneracy. Γ ⊢ σᵢⱼ s : Simplex  if  Γ ⊢ n (S | R) : Cochain ∧ r = σᵢⱼ < s ∧ r ∈ R ∧ s ∈ S
4. Comp Degeneracy. σᵢⱼ (n (S | R)) → s'  if  r = σᵢⱼ < s' ∧ r ∈ R ∧ s' ∈ S
5. Uniq Degeneracy. Γ ⊢ σᵢⱼ s ≡ σᵢⱼ s'  if  Γ ⊢ n (S | R) : CoChain ∧ n (S' | R') : CoChain ∧ s ∈ S ∧ s' ∈ S' ∧ ∀ r = σᵢⱼ < s ∈ R ∧ r' = σᵢⱼ < s' ∈ R'

### Category

1. Formation. Γ ⊢ Category : Set
2. Intro. Γ ⊢ n (O | R) : Category  if  Γ = o₁, …, oₙ, m₁, …, mₖ : Simplex, r₁, …, rₚ ∧ O = (o₁, …, oₙ) ∧ ∀ rⱼ = tⱼ = tⱼ', Γ ⊢ rⱼ : tⱼ = tⱼ' ∧ ∀ tⱼ = mₐ ∘ mᵦ, mₐ, mᵦ ∈ Γ
3. Elim Comp. Γ ⊢ c : Simplex  if  Γ ⊢ n (O | R) : Category ∧ r = c = m₁ ∘ m₂ ∧ r ∈ R ∧ m₁, m₂ ∈ Γ
4. Comp Comp. (m₁ ∘ m₂) (n (O | R)) → c  if  r = c = m₁ ∘ m₂ ∧ r ∈ R ∧ m₁, m₂ ∈ Γ
5. Uniq Comp. Γ ⊢ c ≡ c'  if  Γ ⊢ n (O | R) : Category ∧ n (O' | R') : Category ∧ r = c = m₁ ∘ m₂ ∈ R ∧ r' = c' = m₁' ∘ m₂' ∈ R' ∧ m₁, m₂ ∈ Γ ∧ m₁', m₂' ∈ Γ'

### Monoid

1. Formation. Γ ⊢ Monoid : Set
2. Intro. Γ ⊢ n (M | R) : Monoid  if  Γ = m₁, …, mₙ : Simplex, r₁, …, rₚ ∧ M = (m₁, …, mₙ) ∧ ∀ rⱼ = tⱼ = tⱼ', Γ ⊢ rⱼ : tⱼ = tⱼ' ∧ ∀ tⱼ = mₐ ∘ mᵦ, mₐ, mᵦ ∈ M
3. Elim Comp. Γ ⊢ c : Simplex  if  Γ ⊢ n (M | R) : Monoid ∧ r = c = m₁ ∘ m₂ ∧ r ∈ R ∧ m₁, m₂ ∈ M
4. Comp Comp. (m₁ ∘ m₂) (n (M | R)) → c  if  r = c = m₁ ∘ m₂ ∧ r ∈ R ∧ m₁, m₂ ∈ M
5. Uniq Comp. Γ ⊢ c ≡ c'  if  Γ ⊢ n (M | R) : Monoid ∧ n (M' | R') : Monoid ∧ r = c = m₁ ∘ m₂ ∈ R ∧ r' = c' = m₁' ∘ m₂' ∈ R' ∧ m₁, m₂ ∈ M ∧ m₁', m₂' ∈ M'
   
### Simplex

1. Formation. Γ ⊢ Simplex : Set
2. Intro. Γ ⊢ n (S | R) : Simplex  if  Γ = s₀, …, sₙ : Simplex, r₁, …, rₚ ∧ |S| = n + 1 ∧ ∀ rⱼ = tⱼ = tⱼ', Γ ⊢ rⱼ : tⱼ = tⱼ' ∧ ∀ ∂ᵢ < sₖ, Γ ⊢ ∂ᵢ : sₖ → sₖ₋₁ ∧ ∀ σᵢ < sₖ, Γ ⊢ σᵢ : sₖ → sₖ₊₁
3. Elim Face. Γ ⊢ ∂ᵢ s : Simplex  if  Γ ⊢ n (S | R) : Simplex ∧ r = ∂ᵢ < s ∧ r ∈ R ∧ s ∈ S
4. Elim Degeneracy. Γ ⊢ σᵢ s : Simplex  if  Γ ⊢ n (S | R) : Simplex ∧ r = σᵢ < s ∧ r ∈ R ∧ s ∈ S
5. Comp Face. ∂ᵢ (n (S | R)) → s'  if  r = ∂ᵢ < s' ∧ r ∈ R ∧ s' ∈ S
6. Comp Degeneracy. σᵢ (n (S | R)) → s'  if  r = σᵢ < s' ∧ r ∈ R ∧ s' ∈ S
7. Uniq Face. Γ ⊢ ∂ᵢ s ≡ ∂ᵢ s'  if  Γ ⊢ n (S | R) : Simplex ∧ n (S' | R') : Simplex ∧ s ∈ S ∧ s' ∈ S' ∧ ∀ r = ∂ᵢ < s ∈ R ∧ r' = ∂ᵢ < s' ∈ R'
8. Uniq Degeneracy. Γ ⊢ σᵢ s ≡ σᵢ s'  if  Γ ⊢ n (S | R) : Simplex ∧ n (S' | R') : Simplex ∧ s ∈ S ∧ s' ∈ S' ∧ ∀ r = σᵢ < s ∈ R ∧ r' = σᵢ < s' ∈ R'

### Simplicial

#### Formation

The simplicial type is declared as a set within the context Γ without any premises.

```
Γ ⊢ Simplicial : Set
```

#### Introduction

A simplicial set of rank n with elements S and constraints R is formed from context Γ if simplices, equalities, face maps, and degeneracy maps are properly defined.

```
Γ ⊢ n (S | R) : Simplicial if
Γ = s₀₁, …, sₙₘₙ : Simplex, r₁, …, rₚ ∧
    S₀, S₁, …, Sₙ = (s₀₁, …, s₀ₘ₀), …, (sₙ₁, …, sₙₘₙ) ∧
    rⱼ = tⱼ = tⱼ',
Γ ⊢ rⱼ : tⱼ = tⱼ' ∧
    ∂ᵢⱼ < sₖₗ,
Γ ⊢ ∂ᵢⱼ : sₖₗ → sₖ₋₁,ₘ ∧
    σᵢⱼ < sₖₗ,
Γ ⊢ σᵢⱼ : sₖₗ → sₖ₊₁,ₘ
```

#### Elim Face

The face map ∂ᵢⱼ extracts a simplex from s in a simplicial set if the constraint r defines the face relation.

```
Γ ⊢ ∂ᵢⱼ s : Simplex if
Γ ⊢ n (S | R) : Simplicial ∧
    r = ∂ᵢⱼ < s ∧
    r ∈ R ∧
    s ∈ S                                  
```

#### Elim Composition

The composition s₁ ∘ s₂ yields a simplex c in a simplicial set if the constraint r defines it and s1 and s2 are composable.

```
Γ ⊢ c : Simplex if
Γ ⊢ n (S | R) : Simplicial ∧
    r = c = s₁ ∘ s₂ ∧
    r ∈ R ∧ s₁, s₂ ∈ S ∧
Γ ⊢ ∂ᵢᵢ₋₁ s₁ = ∂ᵢ₀ s₂
```

#### Elim Degeneracy

The degeneracy map σᵢⱼ lifts a simplex s to a higher simplex in a simplicial set if the constraint r defines the degeneracy relation.

```
Γ ⊢ σᵢⱼ s : Simplex if
Γ ⊢ n (S | R) : Simplicial ∧
    r = σᵢⱼ < s,
    r ∈ R,
    s ∈ S
```

#### Face Computation

The face map ∂ᵢⱼ applied to a simplicial set reduces to the simplex s′ specified by the constraint r in R.

```
∂ᵢⱼ (n (S | R)) → s' if
    r = ∂ᵢⱼ < s' ∧
    r ∈ R ∧
    s' ∈ S
```

### Composition Computation.

The composition s₁ ∘ s₂ applied to a simplicial set reduces to the simplex c specified by the constraint r in R, given s1 and s2 are composable.

```
(s₁ ∘ s₂) (n (S | R)) → c if
    r = c = s₁ ∘ s₂ ∧
    r ∈ R ∧
    s₁, s₂ ∈ S ∧
Γ ⊢ ∂ᵢᵢ₋₁ s₁ = ∂ᵢ₀ s₂
```

### Degeneracy Computation.

The degeneracy map σᵢⱼ applied to a simplicial set reduces to the simplex s′ specified by the constraint r in R.

```
σᵢⱼ (n (S | R)) → s' if
    r = σᵢⱼ < s' ∧ 
    r ∈ R ∧ 
    s' ∈ S
```

#### Face Uniqueness

Two face maps ∂ᵢⱼ s and ∂ᵢⱼ s′ are equal if they are defined by constraints r and r′ across two simplicial sets with matching elements.

```
Γ ⊢ ∂ᵢⱼ s ≡ ∂ᵢⱼ s'  if  
Γ ⊢ n (S | R) : Simplicial ∧ 
    n (S' | R') : Simplicial ∧ 
    s ∈ S ∧ s' ∈ S' ∧ 
    r = ∂ᵢⱼ < s ∈ R ∧ 
    r' = ∂ᵢⱼ < s' ∈ R'
```

### Uniqueness of Composition.

Two composed simplices c and c′ are equal if their constraints r and r′ define compositions of matching pairs s₁, s₂ and s₁′, s₂′ across two simplicial sets with composability conditions.

```
Γ ⊢ c ≡ c' if
Γ ⊢ n (S | R) : Simplicial ∧
    n (S' | R') : Simplicial ∧ 
    r = c = s₁ ∘ s₂ ∈ R ∧
    r' = c' = s₁' ∘ s₂' ∈ R' ∧
    s₁, s₂ ∈ S ∧ 
    s₁', s₂' ∈ S' ∧ 
Γ ⊢ ∂ᵢᵢ₋₁ s₁ = ∂ᵢ₀ s₂ ∧ 
Γ ⊢ ∂ᵢᵢ₋₁ s₁' = ∂ᵢ₀ s₂'
```

### Uniqueness of Degeneracy.

Two degeneracy maps σᵢⱼ s and σᵢⱼ s′ are equal if they are defined by constraints r and r′ across two simplicial sets with matching elements.

```
Γ ⊢ σᵢⱼ s ≡ σᵢⱼ s' if
Γ ⊢ n (S | R) : Simplicial ∧
    n (S' | R') : Simplicial ∧
    s ∈ S ∧
    s' ∈ S' ∧
    r = σᵢⱼ < s ∈ R ∧
    r' = σᵢⱼ < s' ∈ R'
```

## Examples

### N-Monoid

```
def nat_monoid : Monoid
 := П (z s : Simplex),
      s ∘ z = s, z ∘ s = s
    ⊢ 2 (z s | s ∘ z = s, z ∘ s = s)
```

O(5).

### Category with Group (Path Category with Z/2Z)

```
def path_z2_category : Category
 := П (x y : Simplex),
      (f g h : Simplex),
      (z2 : Group(П (e a : Simplex), a² = e ⊢ 1 (a | a² = e))),
      f ∘ g = h
    ⊢ 2 (x y | f g h | f ∘ g = h)
```

O(8)—5 context + 2 nested group + 1 constraint—linear with nesting.

### Triangle Chain

```
def triangle_chain : Chain
 := П (v₀ v₁ v₂ e₀₁ e₀₂ e₁₂ t : Simplex),
      ∂₁₀ = e₀₁, ∂₁₁ = e₀₂, ∂₁₂ = e₁₂, ∂₂ < e₀₁ e₀₂ e₁₂
    ⊢ 2 (v₀ v₁ v₂, e₀₁ e₀₂ e₁₂, t | ∂₁₀ ∂₁₁ ∂₁₂, ∂₂)
```

O(11).

### Simplicial Circle

```
def circle : Simplicial
 := П (v e : Simplex),
       ∂₁₀ = v, ∂₁₁ = v, s₀ < v
     ⊢ 1 (v, e | ∂₁₀ ∂₁₁, s₀)
```

O(5).

### Z/3Z

```
def z3 : Group
 := П (e a : Simplex),
      a³ = e
    ⊢ 1 (a | a³ = e)
```

O(4).

### Triangle

```
def triangle : Simplex := П (a b c : Simplex),
         (ab bc ca : Simplex), ac = ab ∘ bc
         ⊢ 2 (a b c | ab bc ca)
```

O(7).

### Singular Cone

```
def singular_cone : Simplex
 := П (p q r s : Simplex),
      (qrs prs pqs : Simplex), pqr = pqs ∘ qrs
    ⊢ 3 (p q r s | qrs prs pqs pqr)
```

Context: p, q, r, s: Simplex (vertices), qrs, prs, pqs : Simplex (faces), pqr = pqs ∘ qrs.

Simplex: Dimension 3, 4 faces.

### Möbius Piece

```
def Möbius : Simplex
 := П (a b c : Simplex),
      (bc ac : Simplex), ab = bc ∘ ac
    ⊢ 2 (a b c | bc ac ab)
```

Context: a, b, c : Simplex (vertices), bc, ac : Simplex (faces), ab = bc ∘ ac (relation).

Simplex: Dimension 2, 3 faces.

### Degenerate Tetrahedron

```
def degen_tetra : Simplex
 := П (p q r s : Simplex, q = r),
      (qrs prs pqs : Simplex), pqr = pqs ∘ qrs
    ⊢ 3 (p q r s | qrs prs pqs pqr)
```

Context: p, q, r, s : Simplex, q = r (degeneracy), qrs, prs, pqs : Simplex, pqr = pqs ∘ qrs.

Simplex: Dimension 3, 4 faces—degeneracy implies a collapsed edge.

Non-Triviality: q = r flattens the structure algebraically, testing composition under equality.

### Twisted Annulus

```
def twisted_annulus : Simplex
 := П (a b c d : Simplex),
      (bc ac bd : Simplex), ab = bc ∘ ac, cd = ac ∘ bd
    ⊢ 2 (a b c | bc ac ab), 2 (b c d | bc bd cd)
```

Context:
* Vertices:  a, b, c, d.
* Faces: bc, ac, bd.
* Relations: ab = bc ∘ ac,  cd = ac ∘ bd  (twist via composition).
  
Simplices:
* (a b c | bc, ac, ab ): First triangle.
* (b c d | bc, bd, cd ): Second triangle, sharing bc.
  
Checking:
* Vertices: a, b, c, d ∈ Γ — O(4).
* Faces: bc, ac, ab (O(3)), bc, bd, cd (O(3)) — total O(6).
* Relations: ab = bc ∘ ac (O(1)), cd = ac ∘ bd (O(1)) — O(2).
* Total: O(12) — linear, fast.

### Degenerate Triangle (Collapsed Edge)

```
def degen_triangle : Simplex
 := П (a b c : Simplex, b = c),
      (bc ac : Simplex), ab = bc ∘ ac
    ⊢ 2 (a b c | bc ac ab)
```

Context: 
* Vertices: a, b, c, with b = c.
* Faces: bc, ac.
* Relation: ab = bc ∘ ac.

Simplex:
* (a b c | bc, ac, ab ) — 3 faces, despite degeneracy.

Checking:
* Vertices: a, b, c ∈ Γ, b = c — O(3).
* Faces: bc, ac, ab ∈ Γ — O(3).
* Relation: ab = bc ∘ ac — O(1).
* Total: O(7)—efficient, handles degeneracy cleanly.

### Singular Prism (Degenerate Face)

```
def singular_prism : Simplex
 := П (p q r s t : Simplex),
      (qrs prs pqt : Simplex, qrs = qrs), pqr = pqt ∘ qrs
    ⊢ 3 (p q r s | qrs prs pqt pqr)
```

Context: 
* Vertices: p, q, r, s, t.
* Faces: qrs, prs, pqt.
* Relations: qrs = qrs (degenerate identity), pqr = pqt ∘ qrs.

Simplex: 
* (p q r s | qrs, prs, pqt, pqr ) — 4 faces, one degenerate.

Checking:
* Vertices: p, q, r, s ∈ Γ (t unused, valid) — O(4).
* Faces: qrs, prs, pqt, pqr ∈ Γ — O(4).
* Relations: qrs = qrs (O(1)), pqr = pqt ∘ qrs (O(1)) — O(2).
* Total: O(10) — linear, fast despite degeneracy.

### S¹ as ∞-Groupoid

```
def s1_infty : Simplicial
 := П (v e : Simplex),
      ∂₁₀ = v, ∂₁₁ = v, s₀ < v,
      ∂₂₀ = e ∘ e, s₁₀ < ∂₂₀
    ⊢ ∞ (v, e, ∂₂₀ | ∂₁₀ ∂₁₁, s₀, ∂₂₀, s₁₀)
```

AST:

```
(* Infinite S¹ ∞-groupoid *)
let s1_infty = {
  name = "s1_infty";
  typ = Simplicial;
  context = [
    Decl (["v"; "e"], Simplex);  (* Base point and loop *)
    Equality ("∂₁₀", Id "v", Id "∂₁₀");
    Equality ("∂₁₁", Id "v", Id "∂₁₁");
    Equality ("s₀", Id "e", Id "s₀");
    Equality ("∂₂₀", Comp (Id "e", Id "e"), Id "∂₂₀");  (* 2-cell: e ∘ e *)
    Equality ("s₁₀", Id "∂₂₀", Id "s₁₀")  (* Degeneracy for 2-cell *)
  ];
  rank = Infinite;  (* Unbounded dimensions *)
  elements = ["v"; "e"; "∂₂₀"];  (* Finite truncation: 0-, 1-, 2-cells *)
  constraints = [
    Eq (Id "∂₁₀", Id "v");
    Eq (Id "∂₁₁", Id "v");
    Map ("s₀", ["v"]);
    Eq (Id "∂₂₀", Comp (Id "e", Id "e"));
    Map ("s₁₀", ["∂₂₀"])
  ]
}
```

### ∞-Category with cube fillers

```
def cube_infty : Category := П (a b c : Simplex),
       (f g h : Simplex), cube2 = g ∘ f, cube2 : Simplex,
       cube3 = cube2 ∘ f, cube3 : Simplex
       ⊢ ∞ (a b c | cube2 cube3)
```

## Bibliography

* Daniel Kan. Abstract Homotopy I. 1955.
* Daniel Kan. Abstract Homotopy II. 1956.
* Daniel Kan. On c.s.s. Complexes. 1957.
* Daniel Kan. A Combinatorial Definition of Homotopy Groups. 1958.

## Conclusion

Dan Kan Simplicity HoTT, hosted at groupoid/dan, is a lightweight, pure type checker
built on Cubical Homotopy Type Theory (CCHM), named in tribute to Daniel Kan for
his foundational work on simplicial sets. With a unified syntax — 
`П (context) ⊢ n (elements | constraints)` — Dan supports a rich type
system `Simplex`, `Group`, `Simplicial`, `Chain`, `Category`, `Monoid`, now extended with 
∞-categories featuring cube fillers.
