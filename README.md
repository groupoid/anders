Anders
======

CCHM homotopy system type checker based on Mini-TT for OCaml.

Features
--------

* MLTT with Leibniz equality (axiomatic J and comp₆) in 500 LOC
* CHM-style primitives with hierarchy of cofibrant pretypes Vₙ in 200 LOC
* Parser in 50 LOC
* Lexer in 50 LOC
* Full Agda-style UTF-8 support including universe levels
* Lean comma-syntax for ΠΣ
* Non-2D syntax with top-level specificators
* Best suited for academic papers

Prerequisites
-------------

```shell
$ apt install ocaml ocamlbuild menhir
```

Try
---

Reality checking.

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
$ ocamlbuild -use-menhir -yaccflag "--explain" anders.native
$ ./anders.native girard check experiments/mltt.anders
```

Papers
------

* <a href="http://www.cse.chalmers.se/~bengt/papers/GKminiTT.pdf">A simple type-theoretic language: Mini-TT</a> [Coquand, Kinoshita, Nordström, Takeyama]
* <a href="https://arxiv.org/pdf/1611.02108.pdf">Cubical Type Theory: a constructive interpretation of the univalence axiom</a> [Cohen, Coquand, Huber, Mörtberg]
* <a href="https://arxiv.org/pdf/1802.01170.pdf">On Higher Inductive Types in Cubical Type Theory</a> [Coquand, Huber, Mörtberg]

Credits
-------

* Siegmentation Fault
* 5HT
