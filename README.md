Anders
======

[![OPAM](https://img.shields.io/github/v/release/groupoid/anders.svg)](https://opam.ocaml.org/packages/anders/)
[![Actions](https://github.com/groupoid/anders/workflows/OCaml/badge.svg)](https://github.com/groupoid/anders/actions)

CCHM homotopy system type checker based on Mini-TT for OCaml.

Features
--------

* Homepage: https://groupoid.space/homotopy
* Fibrant MLTT-style ΠΣ primitives with Leibniz equality in 500 LOC
* Cofibrant CHM-style I primitives with pretypes hierarchy Vₙ in 500 LOC
* Parser in 50 LOC
* Lexer in 50 LOC
* UTF-8 support including universe levels
* Lean syntax for ΠΣ
* 1D syntax with top-level declarations
* Groupoid Infinity CCHM base library: https://groupoid.space/math
* Best suited for academic papers

Setup
-------------

```shell
$ opam install anders
```

Samples
-------

You can find some examples in the `share` directory of the Anders package.
For instance reality checking by internalizing MLTT can be performed by the following usage:

```Lean
def MLTT (A: U) : U := Σ
    (Π-form  : Π (B : A → U), U) -- Pi Type
    (Π-ctor₁ : Π (B : A → U), Pi A B → Pi A B)
    (Π-elim₁ : Π (B : A → U), Pi A B → Pi A B)
    (Π-comp₁ : Π (B : A → U) (a : A) (f : Pi A B), Equ (B a) (Π-elim₁ B (Π-ctor₁ B f) a) (f a))
    (Π-comp₂ : Π (B : A → U) (a : A) (f : Pi A B), Equ (Pi A B) f (λ (x : A), f x))
    (Σ-form  : Π (B : A → U), U) -- Sigma Type
    (Σ-ctor₁ : Π (B : A → U) (a : A) (b : B a), Sigma A B)
    (Σ-elim₁ : Π (B : A → U) (_ : Sigma A B), A)
    (Σ-elim₂ : Π (B : A → U) (x : Sigma A B), B (pr₁ A B x))
    (Σ-comp₁ : Π (B : A → U) (a : A) (b: B a), Equ A a (Σ-elim₁ B (Σ-ctor₁ B a b)))
    (Σ-comp₂ : Π (B : A → U) (a : A) (b: B a), Equ (B a) b (Σ-elim₂ B (a, b)))
    (Σ-comp₃ : Π (B : A → U) (p : Sigma A B), Equ (Sigma A B) p (pr₁ A B p, pr₂ A B p))
    (=-form  : Π (a : A), A → U) -- Identity Type
    (=-ctor₁ : Π (a : A), Equ A a a)
    (=-elim₁ : Π (a : A) (C: D A) (d: C a a (=-ctor₁ a)) (y: A) (p: Equ A a y), C a y p)
    (=-comp₁ : Π (a : A) (C: D A) (d: C a a (=-ctor₁ a)),
       Equ (C a a (=-ctor₁ a)) d (=-elim₁ a C d a (=-ctor₁ a))),
    U
```

```Lean
def instance (A : U) : MLTT A :=
    (Pi A, lambda A, app A, comp₁ A, comp₂ A,
     Sigma A, pair A, pr₁ A, pr₂ A, comp₃ A, comp₄ A, comp₅ A,
     Equ A, refl A, J A, comp₆ A, A)
```

```shell
$ anders girard check mltt.anders
```

Papers
------

Anders was built by strictly following these publications:

* <a href="http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf">A simple type-theoretic language: Mini-TT</a> [Coquand, Kinoshita, Nordström, Takeyama]
* <a href="https://arxiv.org/pdf/1611.02108.pdf">Cubical Type Theory: a constructive interpretation of the univalence axiom</a> [Cohen, Coquand, Huber, Mörtberg]
* <a href="https://arxiv.org/pdf/1802.01170.pdf">On Higher Inductive Types in Cubical Type Theory</a> [Coquand, Huber, Mörtberg]
* <a href="https://arxiv.org/pdf/1607.04156.pdf">Canonicity for Cubical Type Theory</a> [Huber]
* <a href="https://arxiv.org/pdf/1902.06572.pdf">Canonicity and homotopy canonicity for cubical type theory</a> [Coquand, Huber, Sattler]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalsynthetic.pdf">Cubical Synthetic Homotopy Theory</a> [Mörtberg, Pujet]
* <a href="https://staff.math.su.se/anders.mortberg/papers/unifying.pdf">Unifying Cubical Models of Univalent Type Theory</a> [Cavallo, Mörtberg, Swan]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf">Cubical Agda: A Dependently Typed PL with Univalence and HITs</a> [Vezzosi, Mörtberg, Abel]
* <a href="http://www.cse.chalmers.se/~simonhu/misc/hcomp.pdf">A Cubical Type Theory for Higher Inductive Types</a> [Huber]
* <a href="http://www.cse.chalmers.se/~simonhu/papers/p.pdf">Gluing for type theory</a> [Kaposi, Huber, Sattler]

We tried to bring in as little of ourselves as possible. 

HTS
---

Type system with two identities.

* <a href="https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/HTS.pdf">A simple type system with two identity types</a> [Voevodsky]
* <a href="https://arxiv.org/pdf/1705.03307.pdf">Two-level type theory and applications</a> [Annenkov, Capriotti, Kraus, Sattler]
* <a href="https://types21.liacs.nl/download/syntax-for-two-level-type-theory/">Syntax for two-level type theory</a> [Bonacina, Ahrens]

Acknowledgements
----------------

* Univalent People

Authors
-------

* Siegmentation Fault
* 5HT
