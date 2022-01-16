Anders
======

[![OPAM](https://img.shields.io/github/v/release/groupoid/anders.svg)](https://opam.ocaml.org/packages/anders/)
[![Actions](https://github.com/groupoid/anders/workflows/opam/badge.svg)](https://github.com/groupoid/anders/actions)

Modal Homotopy Type System.

Features
--------

* Homepage: https://groupoid.space/homotopy
* Fibrant MLTT-style 0-1-2-Π-Σ-W primitives with Uₙ hierarchy in 500 LOC
* Cofibrant CHM-style I primitives with pretypes hierarchy Vₙ in 500 LOC
* Generalized Transport and Homogeneous Composition core Kan operations
* Partial Elements
* Cubical Subtypes
* Glue types
* Strict Equality on pretypes
* Coequalizer
* Hub Spokes Disc
* Infinitesimal Modality (de Rham Stack)
* Parser in 80 LOC
* Lexer in 80 LOC
* UTF-8 support including universe levels
* Lean syntax for ΠΣW
* Poor man's records as Σ with named accessors to telescope variables
* 1D syntax with top-level declarations
* Groupoid Infinity CCHM base library: https://groupoid.space/math
* Best suited for academic papers and fast type checking

Setup
-------------

```shell
$ opam install anders
```

Samples
-------

You can find some examples in the `share` directory of the Anders package.

```Lean
def comp-Path⁻¹ (A : U) (a b : A) (p : Path A a b) :
  Path (Path A a a) (comp-Path A a b a p (<i> p @ -i)) (<_> a) :=
<k j> hcomp A (∂ j ∨ k) (λ (i : I), [(j = 0) → a, (j = 1) → p @ -i ∧ -k, (k = 1) → a]) (p @ j ∧ -k)

def kan (A : U) (a b c d : A) (p : Path A a c) (q : Path A b d) (r : Path A a b) : Path A c d :=
<i> hcomp A (∂ i) (λ (j : I), [(i = 0) → p @ j, (i = 1) → q @ j]) (r @ i)

def comp (A : I → U) (r : I) (u : Π (i : I), Partial (A i) r) (u₀ : (A 0)[r ↦ u 0]) : A 1 :=
hcomp (A 1) r (λ (i : I), [(r = 1) → transp (<j>A (i ∨ j)) i (u i 1=1)]) (transp(<i> A i) 0 (ouc u₀))

def ghcomp (A : U) (r : I) (u : I → Partial A r) (u₀ : A[r ↦ u 0]) : A :=
hcomp A (∂ r) (λ (j : I), [(r = 1) → u j 1=1, (r = 0) → ouc u₀]) (ouc u₀)

```

```shell
$ anders check library/path.anders
```

MLTT
----

Type Checker is based on classical MLTT-80 with 0, 1, 2 and W-types.

* <a href="https://raw.githubusercontent.com/michaelt/martin-lof/master/pdfs/Bibliopolis-Book-retypeset-1984.pdf">Intuitionistic Type Theory</a> [Martin-Löf]

CCHM
----

Anders was built by strictly following CCHM publications:

* <a href="http://www.cse.chalmers.se/~simonhu/papers/cubicaltt.pdf">CTT: a constructive interpretation of the univalence axiom</a> [Cohen, Coquand, Huber, Mörtberg]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalhits.pdf">On Higher Inductive Types in Cubical Type Theory</a> [Coquand, Huber, Mörtberg]
* <a href="https://arxiv.org/pdf/1607.04156.pdf">Canonicity for Cubical Type Theory</a> [Huber]
* <a href="http://www.cse.chalmers.se/~simonhu/papers/can.pdf">Canonicity and homotopy canonicity for cubical type theory</a> [Coquand, Huber, Sattler]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalsynthetic.pdf">Cubical Synthetic Homotopy Theory</a> [Mörtberg, Pujet]
* <a href="https://staff.math.su.se/anders.mortberg/papers/unifying.pdf">Unifying Cubical Models of Univalent Type Theory</a> [Cavallo, Mörtberg, Swan]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf">Cubical Agda: A Dependently Typed PL with Univalence and HITs</a> [Vezzosi, Mörtberg, Abel]
* <a href="http://www.cse.chalmers.se/~simonhu/misc/hcomp.pdf">A Cubical Type Theory for Higher Inductive Types</a> [Huber]
* <a href="http://www.cse.chalmers.se/~simonhu/papers/p.pdf">Gluing for type theory</a> [Kaposi, Huber, Sattler]
* <a href="https://doi.org/10.1017/S0960129521000311">Cubical Methods in HoTT/UF</a> [Mörtberg]

We tried to bring in as little of ourselves as possible. 

HTS
---

Anders supports classical Homotopy Type System with two identities.

* <a href="https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/HTS.pdf">A simple type system with two identity types</a> [Voevodsky]
* <a href="https://arxiv.org/pdf/1705.03307.pdf">Two-level type theory and applications</a> [Annenkov, Capriotti, Kraus, Sattler]
* <a href="https://types21.liacs.nl/download/syntax-for-two-level-type-theory/">Syntax for two-level type theory</a> [Bonacina, Ahrens]

de Rham
-------

Infinitesimal Modality was added for direct support of Synthetic Differential Geometry.

* <a href="https://arxiv.org/pdf/1310.7930v1.pdf">Differential cohomology in a cohesive ∞-topos</a> [Schreiber]
* <a href="https://arxiv.org/pdf/1806.05966.pdf">Cartan Geometry in Modal Homotopy Type Theory</a> [Cherubini]
* <a href="https://hott-uf.github.io/2017/abstracts/cohesivett.pdf">Differential Cohesive Type Theory</a> [Gross, Licata, New, Paykin, Riley, Shulman, Cherubini]
* <a href="https://arxiv.org/abs/1509.07584">Brouwer's fixed-point theorem in real-cohesive homotopy type theory</a> [Shulman]

Benchmarks
----------

```
$ time make
real    0m4.936s
user    0m1.874s
sys     0m0.670s
```

```
$ time for i in library/* ; do ./anders.native check $i ; done
real    0m2.085s
user    0m1.982s
sys     0m0.105s
```

Acknowledgements
----------------

* Univalent People

Authors
-------

* Siegmentation Fault
* 5HT
