🧊 Anders
=========

[![OPAM](https://img.shields.io/github/v/release/groupoid/anders.svg)](https://opam.ocaml.org/packages/anders/)
[![Actions](https://github.com/groupoid/anders/workflows/opam/badge.svg)](https://github.com/groupoid/anders/actions)

<img src="https://tonpa.guru/stream/2019/img/Anders%20M%C3%B6rtberg.jpeg" width=600>

Modal Homotopy Type System.

```OCaml
type exp =
| EPre of Z.t | EKan of Z.t | EVar of name | EHole                             (* Cosmos *)
| ENat | EZero | ESucc of exp | EIndNat of exp * exp * exp  (* Canonical Natural Numbers *)
| EPi of exp * (name * exp) | ELam of exp * (name * exp) | EApp of exp * exp        (* Π *)
| ESig of exp * (name * exp) | EPair of tag * exp * exp | EFst of exp | ESnd of exp (* Σ *)
| EId of exp | ERef of exp | EJ of exp | EField of exp * string       (* Strict Equality *)
| EEmpty | EIndEmpty of exp                                                         (* 𝟎 *)
| EUnit | EStar | EIndUnit of exp                                                   (* 𝟏 *)
| EBool | EFalse | ETrue | EIndBool of exp                                          (* 𝟐 *)
| EW of exp * (name * exp) | ESup of exp * exp | EIndW of exp * exp * exp           (* W *)
| EPathP of exp | EPLam of exp | EAppFormula of exp * exp               (* Path Equality *)
| EI | EDir of dir | EAnd of exp * exp | EOr of exp * exp | ENeg of exp (* CCHM Interval *)
| ETransp of exp * exp | EHComp of exp * exp * exp * exp               (* Kan Operations *)
| EPartial of exp | EPartialP of exp * exp | ESystem of exp System.t     (* Partial Funs *)
| ESub of exp * exp * exp | EInc of exp * exp | EOuc of exp          (* Cubical Subtypes *)
| EGlue of exp | EGlueElem of exp * exp * exp | EUnglue of exp                (* Glueing *)
| ECoeq of exp | EIota of exp | EResp of exp | EIndCoeq of exp            (* Coequalizer *)
| EDisc of exp | EBase of exp | EHub of exp | ESpoke of exp | EIndDisc of exp    (* Disc *)
| EIm of exp | EInf of exp | EIndIm of exp * exp | EJoin of exp        (* Infinitesimals *)
| EFla of exp | EFlaUnit of exp | EFlaCounit of exp | EIndFla of exp * exp       (* Flat *)
```

Anders is a HoTT proof assistant based on:
  classical MLTT-80 with N, 0, 1, 2, W types;
  CCHM in CHM flavour as cubical type system with hcomp/trans Kan operations;
  HTS sctrict equality on pretypes;
  de Rham stack and Flat modalities;
  Disc and Coequalizer primitives.
We tend not to touch general recursive higher inductive schemes yet,
instead we will try to express as much HIT as possible through W, Coequlizer and Hub Spokes Disc
in the style of HoTT/Coq homotopy library and Three-HIT theorem.

Features
--------

* Homepage: https://anders.groupoid.space/
* Fibrant MLTT-style N-0-1-2-Π-Σ-W primitives with Uₙ hierarchy in 500 LOC
* Cofibrant CHM-style I (PathP) primitives with pretypes hierarchy Vₙ in 500 LOC
* Generalized Transport and Homogeneous Composition core Kan operations
* Partial Elements
* Cubical Subtypes
* Glue types
* Strict Equality on pretypes
* Coequalizer
* Hub Spokes Disc
* Nat in Kernel for spectral goodness under higher homotopies
* Infinitesimal Shape Modality (de Rham Stack)
* Flat Modality (Sharp is derived)
* Parser in 180 LOC
* Lexer in 120 LOC
* Small Kernel in 2000 LOC
* UTF-8 support including universe levels
* Lean syntax for ΠΣW
* Poor man's records as Σ with named accessors to telescope variables
* 1D syntax with top-level declarations
* Groupoid Infinity CCHM Homotopy Library: https://anders.groupoid.space/library/
* Pure basis best suited for academic papers on W-types and well ordered type checking

Setup
-------------

```shell
$ opam install anders
```

Samples
-------

You can find some examples in the `share` directory of the Anders package.

```Lean
def comp-Path⁻¹ (A : U) (a b : A) (p : Path A a b)
  : Path (Path A a a) (comp-Path A a b a p (<i> p @ -i)) (<_> a)
 := <k j> hcomp A (∂ j ∨ k) (λ (i : I), [ (j = 0) → a,
    (j = 1) → p @ -i ∧ -k, (k = 1) → a]) (p @ j ∧ -k)

def kan (A : U) (a b c d : A) (p : Path A a c) (q : Path A b d) (r : Path A a b)
  : Path A c d := <i> hcomp A (∂ i) (λ (j : I), [(i = 0) → p @ j, (i = 1) → q @ j]) (r @ i)

def comp (A : I → U) (r : I) (u : Π (i : I), Partial (A i) r) (u₀ : (A 0)[r ↦ u 0]) : A 1
 := hcomp (A 1) r (λ (i : I), [(r = 1) → transp (<j>A (i ∨ j)) i (u i 1=1)])
    (transp(<i> A i) 0 (ouc u₀))

def ghcomp (A : U) (r : I) (u : I → Partial A r) (u₀ : A[r ↦ u 0]) : A
 := hcomp A (∂ r) (λ (j : I), [(r = 1) → u j 1=1, (r = 0) → ouc u₀]) (ouc u₀)
```

```shell
$ anders check library/book.anders
```

HTS Equations
-------------

```
transpⁱ N φ u₀ = u₀
transpⁱ U φ A = A
transpⁱ (Π (x : A), B) φ u₀ v = transpⁱ B(x/w) φ (u₀ w(i/0)), w = transp-Fill⁻ⁱ A φ v, v : A(i/1)
transpⁱ (Σ (x : A), B) φ u₀ = (transpⁱ A φ (u₀.1), transpⁱ B(x/v) φ(u₀.2)), v = transp-Fillⁱ A φ u₀.1
transpⁱ (Pathʲ A v w) φ u₀ = 〈j〉 compⁱ A [φ ↦ u₀ j, (j=0) ↦ v, (j=1) ↦ w] (u₀ j)
transpⁱ G ψ u₀ = glue [φ(i/1) ↦ t′₁] a′₁ : G(i/1), G = Glue [φ ↦ (T,w)] A
transpⁱ (W (x : A), B) φ (sup a f) = sup (transpⁱ A φ a) (transpⁱ (B(v) → W) φ f), v = transp-Fillⁱ A φ a
transpⁱ (Coequ A B f g) φ (ι₂ b) = ι₂ (transpⁱ B φ b)
transpⁱ (Coequ A B f g) φ (resp a j) = resp (transpⁱ A φ a) j
transpⁱ (Disc S A) φ (base a) = base (transpⁱ A φ a)
transpⁱ (Disc S A) φ (hub f) = hub (transpⁱ (S → Disc S A) φ f)
transpⁱ (Disc S A) φ (spoke f y j) = spoke (transpⁱ (S → Disc S A) φ f) (transpⁱ S φ y) j
transpⁱ (ℑ A) φ (ℑ-unit a) = ℑ-unit (transpⁱ A φ a)
transpⁱ (♭ A) φ (♭-unit a) = ♭-unit (transpⁱ A φ a)
transp⁻ⁱ A φ u = (transpⁱ A(i/1−i) φ u)(i/1−i) : A(i/0)
transp-Fillⁱ A φ u₀ = transpʲ A(i/i∧j) (φ∨(i=0)) u₀ : A
```

```
hcompⁱ N [φ ↦ 0] 0 = 0
hcompⁱ N [φ ↦ S u] (S u₀) = S (hcompⁱ N [φ ↦ u] u₀)
hcompⁱ U [φ ↦ E] A = Glue [φ ↦ (E(i/1), equivⁱ E(i/1−i))] A
hcompⁱ (Π (x : A), B) [φ ↦ u] u₀ v = hcompⁱ B(x/v) [φ ↦ u v] (u₀ v)
hcompⁱ (Σ (x : A), B) [φ ↦ u] u₀ = (v(i/1), compⁱ B(x/v) [φ ↦ u.2] u₀.2), v = hcomp-Fillⁱ A [φ ↦ u.1] u₀.1
hcompⁱ (Pathʲ A v w) [φ ↦ u] u₀ = 〈j〉 hcompⁱ A [ φ ↦ u j, (j = 0) ↦ v, (j = 1) ↦ w ] (u₀ j)
hcompⁱ G [ψ ↦ u] u₀ = glue [φ ↦ t₁] a₁ : G, G = Glue [φ ↦ (T,w)] A, t₁ = u(i/1) : T, a₁ = unglue u(i/1) : A, glue [φ ↦ t₁] a1 = t₁ : T
hcompⁱ (W (x : A), B) [φ ↦ sup a f] (sup a₀ f₀) = sup (hcompⁱ A [φ ↦ a] a₀) (hcompⁱ (B(v) → W) [φ ↦ f] f₀), v = hcomp-Fillⁱ A [φ ↦ a] a₀
hcompⁱ (Coequ A B f g) [φ ↦ ι₂ u] (ι₂ u₀) = ι₂ (hcompⁱ B [φ ↦ u] u₀)
hcompⁱ (Coequ A B f g) [φ ↦ resp a j] (resp a₀ j) = resp (hcompⁱ A [φ ↦ a] a₀) j
hcompⁱ (Disc S A) [φ ↦ base a] (base a₀) = base (hcompⁱ A [φ ↦ a] a₀)
hcompⁱ (Disc S A) [φ ↦ hub f] (hub f₀) = hub (hcompⁱ (S → Disc S A) [φ ↦ f] f₀)
hcompⁱ (Disc S A) [φ ↦ spoke f y j] (spoke f₀ y₀ j) = spoke (hcompⁱ (S → Disc S A) [φ ↦ f] f₀) (hcompⁱ S [φ ↦ y] y₀) j
hcompⁱ (ℑ A) [φ ↦ ℑ-unit u] (ℑ-unit u₀) = ℑ-unit (hcompⁱ A [φ ↦ u] u₀)
hcompⁱ (♭ A) [φ ↦ ♭-unit u] (♭-unit u₀) = ♭-unit (hcompⁱ A [φ ↦ u] u₀)
hсomp-Fillⁱ A [φ ↦ u] u₀ = hcompʲ A [φ ↦ u(i/i∧j), (i=0) ↦ u₀] u₀ : A
```

MLTT
----

Type Checker is based on classical MLTT-80 with 0, 1, 2 and W-types.

* <a href="https://5ht.co/mltt-80.pdf">Intuitionistic Type Theory</a> [Martin-Löf]

CCHM
----

Anders was built by strictly following CCHM publications:

* <a href="https://arxiv.org/pdf/1611.02108">CTT: a constructive interpretation of the univalence axiom</a> [Cohen, Coquand, Huber, Mörtberg]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalhits.pdf">On Higher Inductive Types in Cubical Type Theory</a> [Coquand, Huber, Mörtberg]
* <a href="https://arxiv.org/pdf/1607.04156.pdf">Canonicity for Cubical Type Theory</a> [Huber]
* <a href="https://arxiv.org/pdf/1607.04156">Canonicity and homotopy canonicity for cubical type theory</a> [Coquand, Huber, Sattler]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalsynthetic.pdf">Cubical Synthetic Homotopy Theory</a> [Mörtberg, Pujet]
* <a href="https://staff.math.su.se/anders.mortberg/papers/unifying.pdf">Unifying Cubical Models of Univalent Type Theory</a> [Cavallo, Mörtberg, Swan]
* <a href="https://staff.math.su.se/anders.mortberg/papers/cubicalagda.pdf">Cubical Agda: A Dependently Typed PL with Univalence and HITs</a> [Vezzosi, Mörtberg, Abel]
* <a href="https://simhu.github.io/misc/hcomp.pdf">A Cubical Type Theory for Higher Inductive Types</a> [Huber]
* <a href="https://drops.dagstuhl.de/storage/00lipics/lipics-vol131-fscd2019/LIPIcs.FSCD.2019.25/LIPIcs.FSCD.2019.25.pdf">Gluing for type theory</a> [Kaposi, Huber, Sattler]
* <a href="https://doi.org/10.1017/S0960129521000311">Cubical Methods in HoTT/UF</a> [Mörtberg]

We tried to bring in as little of ourselves as possible.

HTS
---

Anders supports classical Homotopy Type System with two identities.

* <a href="https://www.math.ias.edu/vladimir/sites/math.ias.edu.vladimir/files/HTS.pdf">A simple type system with two identity types</a> [Voevodsky]
* <a href="https://arxiv.org/pdf/1705.03307.pdf">Two-level type theory and applications</a> [Annenkov, Capriotti, Kraus, Sattler]
* <a href="https://hott-uf.github.io/2021/HoTTUF_2021_paper_5.pdf">Syntax for two-level type theory</a> [Bonacina, Ahrens]

Modalities
----------

Infinitesimal Modality was added for direct support of Synthetic Differential Geometry.

* <a href="https://arxiv.org/pdf/1310.7930v1.pdf">Differential cohomology in a cohesive ∞-topos</a> [Schreiber]
* <a href="https://arxiv.org/pdf/1806.05966.pdf">Cartan Geometry in Modal Homotopy Type Theory</a> [Cherubini]
* <a href="https://hott-uf.github.io/2017/abstracts/cohesivett.pdf">Differential Cohesive Type Theory</a> [Gross, Licata, New, Paykin, Riley, Shulman, Cherubini]
* <a href="https://arxiv.org/pdf/1509.07584">Brouwer's fixed-point theorem in real-cohesive homotopy type theory</a> [Shulman]
* <a href="https://5ht.co/three.pdf">Three-HIT theorem</a> [Bauer, van der Weide]

Benchmarks
----------

Intel i5-12400 or M4: Compilation in three seconds, full library type checks in one minute with K(G,n)-η.

```
% dune build
3.19s user 2.64s system 135% cpu 4.297 total
```

```
% dune exec anders profile check library/book.anders
0.06s user 0.05s system 8% cpu 1.188 total
```

# Anders: Homotopy Library

Here is given the Anders Homotopy Library.

### Foundations

In the `foundations` folder presented the MLTT, Modal and Univalent base libraries:

```
anders.groupoid.space/foundations/
├── mltt/
│   ├── bool/
│   ├── either/
│   ├── fin/
│   ├── induction/
│   ├── list/
│   ├── maybe/
│   ├── mltt/
│   ├── nat/
│   ├── pi/
│   ├── sigma/
│   └── vec/
├── modal/
│   ├── flat/
│   ├── sharp/
│   ├── modality/
│   └── infinitesimal/
└── univalent/
    ├── equiv/
    ├── hedberg/
    ├── extensionality/
    ├── iso/
    ├── path/
    └── prop/
```

### Mathematics

In the `mathematics` folder you will find Mathematical Components for HTS:

```
anders.groupoid.space/mathematics/
├── algebra/
│   ├── algebra/
│   ├── homology/
│   └── int/
├── analysis/
│   ├── real/
│   └── topology/
├── categories/
│   ├── abelian/
│   ├── category/
│   ├── functor/
│   ├── topos/
│   └── groupoid/
├── geometry/
│   ├── bundle/
│   ├── etale/
│   └── formalDisc/
└── homotopy/
    ├── KG1/
    ├── KGn/
    ├── S1/
    ├── Sn/
    ├── coequalizer/
    ├── disc/
    ├── hopf/
    ├── loop/
    ├── pcoequ/
    ├── colimit/
    ├── pullback/
    ├── pushout/
    ├── quotient/
    ├── quotient2/
    ├── suspension/
    └── truncation/
```

## Usage

The main purpose of Anders is doing Homotopy Theory:

```
$ dune exec anders repl

Anders Proof Assistant version 5.1.0
Copyright © 2016–2026 Groupoid Infinity.

For help type ‘:h’.

>
```

Mentions
--------

* Максим Сохацький. <a href="https://www.youtube.com/watch?v=KHDgytozLv4">Презентація кубічного CCHM прувера Anders 0.7.2</a>. 2021-07-18
* Максим Сохацький. <a href="https://tonpa.guru/stream/2022/2022-01-17%20Anders.htm">Anders: верификатор математики</a>. 2022-01-17
* Максим Сохацький. <a href="https://groupoid.github.io/anders/doc/anders.pdf">Anders: Modal Homotopy Type System</a>. 2022-01-17
* Максим Сохацький. <a href="https://axio.groupoid.space">Система формальних мов Групоїд Інфініті</a>. 2024-11-26
