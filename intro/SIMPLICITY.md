# Simplicial HoTT

TLDR: Groupoid Infinity Simplicial HoTT pure algebraїc opetope implementation with explicit syntaxt for fastest type checking.

## Abstract

We present a domain-specific language (DSL) extension to Cubical Homotopy Type Theory (CCHM) for simplicial structures,
designed as a fast type checker with a focus on algebraic purity. Built on the Cohen-Coquand-Huber-Mörtberg (CCHM)
framework, our DSL employs a Lean/Anders-like sequent syntax (П (context) ⊢ k [v₀ .. vₖ] { f₀, ..., fₗ } : Simplex) to define 
k-dimensional simplices via explicit contexts, vertex lists, and face relations, eschewing geometric coherence terms
in favor of compositional constraints (e.g., f=g∘h). The semantics, formalized as inference rules in a Martin-Löf
Type Theory (MLTT)-like setting, include Formation, Introduction, Elimination, Composition, Computational, and
Uniqueness rules, ensuring a lightweight, deterministic computational model with linear-time type checking (O(k + m + n),
where k is vertices, m is faces, and n is relations). Inspired by opetopic purity, our system avoids cubical
path-filling (e.g., PathP), aligning with syntactic approaches to higher structures while retaining CCHM’s
type-theoretic foundation. Compared to opetopic sequent calculi and the Rzk prover, our DSL balances algebraic
simplicity with practical efficiency, targeting simplicial constructions over general ∞-categories,
and achieves a fast, pure checker suitable for formal proofs and combinatorial reasoning.

## Syntax

Incorporating into CCHM/CHM HTS Anders core.

### General Definition

```
def <name> : Simple := <context> ⊢ n [v₀ .. vₙ] { f₀, ..., fₙ } 
```

### Formal BNF

```
<program> ::= "def" <identifier> ":" "Simplex" ":=" <sequent-term>
<sequent-term> ::= "П" "(" <context> ")" <simplex-def> "⊢" <number> "[" <vertex-list> "]" "{" <face-list> "}"
<context> ::= <hypothesis> | <hypothesis> "," <context>
<hypothesis> ::= <identifier> ":" "Simplex" | "(" <face-decls> ")" | <identifier> "=" <identifier> "∘" <identifier>
<face-decls> ::= <identifier> ":" "Simplex" | <identifier> ":" "Simplex" "," <face-decls>
<vertex-list> ::= <identifier> | <identifier> <vertex-list>
<face-list> ::= <face> | <face> "," <face-list>
<face> ::= <identifier>
```

## Semantics

### Formation

```
\frac{}{\Gamma \vdash \text{Simplex} : \text{Set}} \quad (\text{Simplex-Form})
```

### Introduction

```
\frac{
  \Gamma = v_0 : \text{Simplex}, \dots, v_k : \text{Simplex}, e_1, \dots, e_p, f_0 : \text{Simplex}, \dots, f_m : \text{Simplex}, r_1, \dots, r_n \\
  \{ v_0, \dots, v_k \} = \text{vertices in } [v_0 \, \dots \, v_k] \text{ after applying equalities } e_i \\
  \{ f_0, \dots, f_l \} = \{ f_0, \dots, f_m \} \cup \{ f_i \mid r_j = f_i = g \circ h \} \\
  |\text{set } \{ f_0, \dots, f_l \}| = k + 1 \\
  \text{for each } e_i = v_a = v_b, \, \Gamma \vdash v_a = v_b \\
  \text{for each } r_j = f_i = g \circ h, \, \Gamma \vdash \partial_0 g = \partial_k h
}{
  \Gamma \vdash k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex}
} \quad (\text{Simplex-Intro})
```

### Elimination (Simplex-Face)

```
\frac{ \Gamma \vdash k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \quad i : \text{Fin}(k+1)}
     { \Gamma \vdash \partial_i \, (k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \}) \Rightarrow f_i } \quad (\text{Simplex-Face})
```

### Composition 

```
\frac{\Gamma \vdash g : \text{Simplex} \quad \Gamma \vdash h : \text{Simplex} \\
      \Gamma \vdash \partial_0 g = \partial_k h }
     {\Gamma \vdash g \circ h : \text{Simplex}} \quad (\text{Composition})
```

### Computation

Face Extraction:

```
\partial_i \, (k [v_0 \, \dots \, v_k] \{ f_0, f_1, \dots, f_l \}) \to f_i
```

Composition Reduction:

```
f_i \to g \circ h \quad \text{if } \Gamma \text{ contains } f_i = g \circ h
```

Degeneracy Reduction:

```
k [v_0 \, \dots \, v_i \, v_{i+1} \, \dots \, v_k] \{ f_0, \dots, f_l \} 
\to (k-1) [v_0 \, \dots \, v_{i-1} \, v_{i+1} \, \dots \, v_k] 
  \{ f_0', \dots, f_{l-1}' \} \quad \text{if } v_i = v_{i+1} \text{ in } \Gamma
```

Base Case:

```
0 [v] \{ \} \to v
```

### Uniqueness

Uniqueness of Face Extraction (Simplex-Uniqueness-Face):

```
\frac{ \Gamma \vdash s = k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \\
       \Gamma \vdash t = k [v_0 \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \\
       \Gamma \vdash \partial_i \, s = \partial_i \, t \quad (\text{for all } i) }
     { \Gamma \vdash s = t} \quad (\text{Simplex-Uniqueness-Face})
```

Uniqueness of Composition (Composition-Uniqueness):

```
\frac{ \Gamma \vdash f = g \circ h : \text{Simplex} \\
       \Gamma \vdash f' = g' \circ h' : \text{Simplex} \\
       \Gamma \vdash g = g' \quad \Gamma \vdash h = h' \\
       \Gamma \vdash \partial_0 g = \partial_k h \quad \Gamma \vdash \partial_0 g' = \partial_k h'}
     { \Gamma \vdash f = f' } \quad (\text{Composition-Uniqueness})
```

Uniqueness of Degeneracy (Degeneracy-Uniqueness):

```
\frac{ \Gamma \vdash s = k [v_0 \, \dots \, v_i \, v_{i+1} \, \dots \, v_k] \{ f_0, \dots, f_l \} : \text{Simplex} \\
       \Gamma \vdash t = (k-1) [v_0 \, \dots \, v_{i-1} \, v_{i+1} \, \dots \, v_k] \{ f_0', \dots, f_{l-1}' \} : \text{Simplex} \\
       \Gamma \vdash v_i = v_{i+1} \\
       \Gamma \vdash \partial_j s = \partial_j t \quad (\text{for all } j, \text{ adjusted indices}) }
     { \Gamma \vdash s = t } \quad (\text{Degeneracy-Uniqueness})
```

## Examples

### Singular Cone

```
def singular_cone : Simplex
 := П (p q r s : Simplex), 
      (qrs prs pqs : Simplex), pqr = pqs ∘ qrs 
    ⊢ 3 [p q r s] { qrs, prs, pqs, pqr }
```

Context: p, q, r, s: Simplex (vertices), qrs, prs, pqs : Simplex (faces), pqr = pqs ∘ qrs.
Simplex: Dimension 3, 4 faces.

### Möbius Piece

```
def Möbius : Simplex
 := П (a b c : Simplex), 
      (bc ac : Simplex), ab = bc ∘ ac 
    ⊢ 2 [a b c] { bc, ac, ab }
```

Context: a, b, c : Simplex (vertices), bc, ac : Simplex (faces), ab = bc ∘ ac (relation).
Simplex: Dimension 2, 3 faces.

### Degenerate Tetrahedron

```
def degen_tetra : Simplex
 := П (p q r s : Simplex, q = r), 
      (qrs prs pqs : Simplex), pqr = pqs ∘ qrs 
    ⊢ 3 [p q r s] { qrs, prs, pqs, pqr }
```

Context: p, q, r, s : Simplex, q = r (degeneracy), qrs, prs, pqs : Simplex, pqr = pqs ∘ qrs.
Simplex: Dimension 3, 4 faces—degeneracy implies a collapsed edge.
Non-Triviality: q = r flattens the structure algebraically, testing composition under equality.

### Twisted Annulus

```
def twisted_annulus : Simplex
  := П (a b c d : Simplex), 
       (bc ac bd : Simplex), ab = bc ∘ ac, cd = ac ∘ bd
     ⊢ 2 [a b c] { bc, ac, ab }, 2 [b c d] { bc, bd, cd }
```

Context:
* Vertices:  a, b, c, d.
* Faces: bc, ac, bd.
* Relations: ab = bc ∘ ac,  cd = ac ∘ bd  (twist via composition).
Simplices:
* [a b c] { bc, ac, ab }: First triangle.
* [b c d] { bc, bd, cd }: Second triangle, sharing bc.
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
    ⊢ 2 [a b c] { bc, ac, ab }
```

Context: 
* Vertices: a, b, c, with b = c.
* Faces: bc, ac.
* Relation: ab = bc ∘ ac.
Simplex:
* [a b c] { bc, ac, ab } — 3 faces, despite degeneracy.
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
    ⊢ 3 [p q r s] { qrs, prs, pqt, pqr }
```

Context: 
* Vertices: p, q, r, s, t.
* Faces: qrs, prs, pqt.
* Relations: qrs = qrs (degenerate identity), pqr = pqt ∘ qrs.
Simplex: 
* [p q r s] { qrs, prs, pqt, pqr } — 4 faces, one degenerate.
Checking:
* Vertices: p, q, r, s ∈ Γ (t unused, valid) — O(4).
* Faces: qrs, prs, pqt, pqr ∈ Γ — O(4).
* Relations: qrs = qrs (O(1)), pqr = pqt ∘ qrs (O(1)) — O(2).
* Total: O(10) — linear, fast despite degeneracy.

## Conclusion

Rzk supports synthetic ∞-categories via simplicial Homotopy Type Theory (sHoTT), extending MLTT with:
Shapes: Simplicial shapes (e.g., Δn) as types, representing n-simplices.
Topes: Geometric constraints (e.g., i=j, i≤k) over the interval I, enforced by a tope solver.
Higher Paths: Hom_A(x,y) as path types over shapes, supporting higher morphisms (e.g., 2-morphisms, 3-morphisms).
Type Checking: Bidirectional with a tope solver — O(n + solver cost), where solver cost varies (e.g., O(n²) or worse for complex constraints).
Expressiveness: Models ∞-categories (e.g., Kan complexes, ∞-groupoids) with infinite-dimensional coherences.
Our DSL currently handles finite-dimensional simplices (e.g., k-simplices with k+1 faces) with explicit compositions—no shapes, topes, or higher paths.

Adding ∞-category support akin to the Rzk prover to our Lean/Anders-like simplicial
DSL in CCHM would significantly impact type checking speed, shifting it from our
current lightweight, linear-time design (O(k + m + n)) to a more complex system
with potentially higher computational costs. 

Our CCHM DSL is a fast, pure simplicial checker—aligned with opetopic purity in its algebraic core,
but distinct in its fixed-face simplicial structure and CCHM reductions. Compared to Rzk, it sacrifices
generality for speed and simplicity, embedding a lean DSL in a type-theoretic framework. It’s a sweet
spot—opetopic-inspired, MLTT-rigorous, and CCHM-efficient—ideal for compact, non-trivial simplicial constructions.

A lightweight, fast type checker—O(k + m + n)—balancing opetopic purity (algebraic,
no geometry) with CCHM’s computational power (reductions, uniqueness). It’s less
expressive than Rzk (no ∞-categories) and less flexible than opetopes (fixed faces vs. trees),
but excels at simplicial tasks. Ours is O(k + m + n)—faster than potential O(n log n) tree
traversals in opetopic derivations, due to fixed structure and no recursion.

Both avoid geometric filling—our DSL uses explicit face compositions (e.g., ab = bc ∘ ac),
akin to opetopic grafting, while opetopes rely on tree-based pasting (e.g., Γ ⊢ o).
We’re purer than traditional simplicial sets (no coh). Opetopes lack computational
reductions—ours adds MLTT-like rules (∂_i → f_i), diverging from static syntax but enhancing usability in CCHM.
