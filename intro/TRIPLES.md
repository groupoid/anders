<h1>Introduction</h1>

<p>Type theory is a universal programming language of pure mathematics (for proving theorems),
   which can contain an arbitrary number of consistent axioms, ordered in the form of
   pseudo-isomorphisms: the functions encode (ways of constructing type elements)
   and decode (dependent eliminators of the universal principle of type induction),
   and their equations—beta and eta rules of computability and uniqueness.
   Usually, type theory, as a programming language, already includes basic
   primitives (axioms in the form of built-in types) and accompanying
   documentation explaining their application in the form of lectures or summaries.</p>

<p>Adjunction triples provide a structural foundation for understanding
   the interaction of dependent types in type theory. In the context of
   Martin-Löf Type Theory (MLTT), the four fundamental type rules—formation,
   introduction, elimination, and computation—correspond to different
   aspects of isomorphism within these adjunctions. This perspective
   allows us to analyze the behavior of &Pi; and &Sigma; types systematically.</p>

<h1>Fibrational setting</h1>

<p>In this framework, the &Pi; type represents universally quantified dependent functions,
while the &Sigma; type models dependent pairs. Their interpretations extend into various
branches of mathematics, each highlighting a distinct perspective on their structural role.
Below, we explore four such perspectives: categorical, set-theoretic, homotopical, and groupoidal.</p>

<h2>1. Categorical Perspective: &Pi; and &Sigma; as Adjunctions (Kock-Wright Interpretation)</h2>

<p>From a categorical viewpoint, &Pi; and &Sigma; types arise naturally through adjunctions.
The key idea is that dependent function types correspond to right adjoints, while dependent
sum types correspond to left adjoints. This perspective, pioneered by Kock and Wright,
provides a logical foundation for interpreting these types in categorical models of type theory.</p>

<p>The adjunctions can be explicitly formulated as triples:</p>
<ul>
    <li>(&Sigma;<sub>f</sub> &vdash; f* &vdash; &Pi;<sub>f</sub>): Given a fibration p: E &rarr; B,
        the &Sigma; type corresponds to the left adjoint &Sigma;<sub>f</sub>, the base change
        functor f* is the middle functor, and the &Pi; type corresponds to the
        right adjoint &Pi;<sub>f</sub>.</li>
    <li>This aligns with the categorical interpretation of &Pi; as an exponential
        object B<sup>A</sup> in a suitable category and &Sigma; as a dependent coproduct.</li>
</ul>

<h2>2. Set-Theoretic Perspective: &Sigma; and Constructive Axiom of Choice</h2>

<p>In classical set theory, &Sigma; types naturally model the totality of relations by encoding dependent pairs (x, y) where y depends on x. This is crucial in constructive mathematics, where the axiom of choice does not hold unrestrictedly.</p>

<h2>3. Homotopical Perspective: &Pi; Types as Fiber Bundles</h2>

<p>In homotopy type theory, &Pi; and &Sigma; types correspond to fiberwise constructions in homotopy theory.</p>

<ul>
    <li>Given a fibration p: E &rarr; B, the &Sigma; type represents the total space E,
        while the &Pi; type represents the space of sections &Pi;<sub>x</sub> P(x),
        which generalizes function spaces in homotopy theory.</li>

    <li>The key homotopy-theoretic result is the isomorphism:<br> &Pi;<sub>x</sub> P(x) &cong; Hom(B, E)</li>
</ul>

<h1>Identification setting</h1>

<h2>4. Groupoidal Perspective: Identity Systems and the Cubical Model</h2>

<p>In the intensional theory of types, the type of equality is also built in
   as type-theoretical primitives of the categorical meta-theoretical model
   of conjugations of three Jacobs-Lavir functors:</p>

<ul>
    <li>Factor space (Q)</li>
    <li>Identification system (=)</li>
    <li>Contractible space (C)</li>
</ul>


<p>These functors form another adjunction:</p>
<ul>
    <li>(Q &vdash; = &vdash; C): The factor space functor Q is the left adjoint,
        the identification system = serves as the base functor, and the contractible
        space functor C is the right adjoint.</li>
</ul>

<h1>Conclusion</h1>

<p>The interplay between &Pi; and &Sigma; types across different mathematical
   disciplines showcases their fundamental nature. Whether understood categorically
   as adjunctions, set-theoretically as constructive choice principles, homotopically
   as fiber bundle structures, or groupoidally as identity systems, these types form
   the backbone of constructive homotopy type theory. The CCHM model strengthens
   these interpretations by ensuring computational validity, making it a powerful
   foundation for both mathematical reasoning and formal verification in proof
   assistants such as Agda, Coq, and Lean.</p>
