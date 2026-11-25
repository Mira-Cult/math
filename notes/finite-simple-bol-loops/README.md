# Bol loops

<a id="finite-simple-bol-loops"></a>

**Mira Cult**

This workspace brings together results on Bol loops, their translation groups, and their connections to graphs and analysis. A central goal is to classify **all finite simple Bol loops up to isomorphism**: give constructions, prove they exhaust the possibilities, and decide when they give the same loop. **The unrestricted classification remains open.**

[Results](RESULTS.md) · [Claim catalogue](CLAIMS.md) · [Classification map](CLASSIFICATION.md) · [Proof sources](sources/README.md)

## Burnside and Hall–Sylow questions

- [Burnside questions at exponent three](bol-burnside/README.md). The free Bol loop of exponent three on two generators is infinite, but its matched one-sided translation group is locally a finite 3-group. The explicit loop construction works at every odd prime exponent.
- [Odd-order loops without Sylow subloops](odd-bol-hall/README.md). A solvable Bol loop of order 63 has no nine-element subloop. A uniform construction gives a counterexample at every odd prime.

## Odd orders: the first simple example and a full prime-cube list

[Odd two-prime orders](odd-prime-pair/README.md) now have an exact least exponent and a complete census there. The next exponent is impossible. At the third exponent in the ternary order-nine case the elementary-core loops have an exact count; [the higher-rotation minimum for abelian cores](odd-prime-pair/manuscripts/0135-higher-cyclic-abelian-cores.md) now excludes elementary cores outside the ternary order-nine case and gives sharp minimum orders for all abelian cores at each prescribed higher cyclic top.

The [prime-top two-type theorem](odd-prime-pair/manuscripts/0134-prime-top-two-types.md) classifies **every** finite simple proper left Bol loop at $`qp^{2p+2}`$ when $`\mathrm{ord}_q(p)=p`$. There are exactly two ordinary isomorphism types, including at order **85,293**.

The [least odd order](odd-degree/README.md) of a finite simple nonassociative left Bol loop is **1053**. Nagy constructed an example; the new argument rules out every smaller odd order. The same package gives [the complete list at order *p*³ for primes *p* ≥ 5](odd-degree/manuscripts/all-bol-loops-of-prime-cube-order.md), up to isomorphism and isotopy. Neither result asserts uniqueness at 1053. [Separate proof reviews and reproducible checks](odd-degree/verification.md).

## Extraspecial cores at two-prime orders

For every pair of odd primes *p*, *q* with *p* dividing *q* − 1, [an explicit construction](extraspecial-cores/README.md) gives simple proper Bol loops with extraspecial *p*-core in the left multiplication group. Mixing two kinds of representation gives [arbitrarily many pairwise nonisotopic loops at one order](extraspecial-cores/axial-cotangent-extraspecial-multiplicity.md). These are multiplicity lower bounds, not a census.

## Which groups can be right nuclei?

[Exactly the finite groups of odd order](right-nuclei/README.md) occur as entire right nuclei of finite simple proper odd Bol loops. Given such a group *R*, [any prescribed subgroup of its center](right-nuclei/proofs/central-intersection.md) can be exactly the nuclear right translations that also lie in the left multiplication group. This classifies an invariant, not all loops.

<a id="latest-classification-advances-17-november-2026"></a>
<a id="current-classification-checkpoint"></a>
<a id="what-we-have-achieved"></a>

<a id="a-construction-a-simple-loop-of-exponent-six"></a>

## How many loops can share one order and one quotient?

[The projective construction](projective-radicals/README.md) gives at least $`3^{s^3/4}`$ pairwise nonisotopic simple exponent-six loops of one order for each $`s\ge21`$. Their left multiplication groups all have quotient PSL₂(19). Another choice gives [one radical containing every bounded-size group of class at most two and exponent dividing three](projective-radicals/proofs/universal-group-host.md), at logarithmic host cost of optimal quadratic order. These are group embeddings, not automatically loop embeddings.

## A nested family of simple loops of exponent six

[A simple left Bol loop of exponent six](manuscripts/0112-elementary-radical-example.md) has order $`20\cdot3^{119}`$ and no element of order five, even though five divides its order. Its faithful left multiplication group is $`(\mathbb F_3^{236},+)\rtimes\mathrm{PSL}_2(19)`$. The [matrix data and two verifiers](sources/elementary-psl2-19/README.md) make the computer-assisted construction reproducible. The exact example received independent AI mathematical review.

[The infinite augmentation chain](manuscripts/0113-infinite-augmentation-chain.md) embeds that loop into successively larger simple proper left Bol loops. Stage $`n`$ has order $`20\cdot3^{119+19n}`$, every stage has exponent six, and their union is a countably infinite locally finite simple loop. The proof keeps each old multiplication intact by extending its selected coset translations. The [chain programs and audit](sources/augmentation-chain/README.md) cover the induction and actual embeddings; this is a construction, not an exhaustion theorem.

## The classification picture

Three kinds of progress fit together; none can replace the others.

- **Restrict the full multiplication group.** The conditional full-socle exclusions cover all sporadic and exceptional Lie-type families, PSL₂ and odd-dimensional PSL/PSU, all characteristic-two PSL/PSU, PSL₄ and PSU₄ over every field, and binary Sp₂ₘ(2) for m≥3. Alternating full socles force the natural action. See the [family map](CLASSIFICATION.md) and [precise statements](CLAIMS.md).
- **Classify operations within specified envelopes.** Results include radical-free PSL₂/A₅ models, [abelian-top path parameters](manuscripts/0068-abelian-nilpotent-path-parameters.md), and [affine-square operations](manuscripts/0099-affine-square-factor-exchange.md). In the [binary quadratic-refinement action](manuscripts/0097-binary-symplectic-full-socles-and-actions.md), the only possible loop is the 120-element Paige loop, not a new proper Bol loop.
- **Control extensions and construct new families.** The [odd-kernel orbit and lift theory](manuscripts/0098-odd-kernel-stabilizer-orbits.md) gives exact local constraints and finite-data assembly with a distinguished elementary layer. Other constructions demonstrate how broad the classification must be; the [proposed non-G-loop, non-Bruck-isotopic example](0018-non-g-loop-non-bruck-context.md) addresses Nagy's existence question.

The [matched natural tensor exclusion](manuscripts/0100-matched-tensor-radicals.md) rules out an entire matrix-radical family in rank at least three, including the exceptional binary rank-three case. Above a [faithful irreducible odd layer](manuscripts/0101-odd-kernel-block-action.md), the kernel of the action on blocks now has trivial solvable radical, even without a splitting hypothesis.

When the left multiplication group has a nontrivial solvable radical, the [canonical elementary descent](manuscripts/0102-canonical-elementary-descent.md) now gives exact recognition and loop-isomorphism tests on quotient and module data without assuming a split extension. Which data actually occur in structural families remains open.

For a [radical-free left group](manuscripts/0103-radical-free-socle-coordinates.md), simple factors now give a complementary recognition and isomorphism test that sees every normal subgroup. There is also a restriction on both branches: in [every abelian quotient](manuscripts/0104-twisted-stabilizer-derangements.md), doubling the quotient gives a subgroup whose size divides each orbit of the inversion-conjugate point stabilizer. A [nilpotent transitive action on at least two isomorphic socle factors](manuscripts/0105-nilpotent-socle-stabilizer-projections.md) forces the actual point-stabilizer intersection to project nontrivially and properly onto every factor. For [an entire even-field PSL₂ socle](manuscripts/0106-nilpotent-transitive-even-field-psl2.md), no transitive nilpotent factor action survives, including fields of size four and nonregular permutation groups. For [any simple type with odd outer automorphism group](manuscripts/0107-odd-outer-nilpotent-socles.md), a transitive nilpotent action on a whole socle power of degree at least two is likewise impossible. More generally, any [nilpotent transitive action on a whole simple socle power is a 2-group](manuscripts/0109-nilpotent-socle-actions-are-two-groups.md); it has both an unpermuted mark and an entirely paired mark. For [alternating factors](manuscripts/0110-nilpotent-transitive-alternating-socles.md), the 2-group case is impossible in every degree. The same exclusion holds for [projective-line factors in every characteristic](manuscripts/0111-nilpotent-transitive-projective-line-socles.md); the odd-field proof controls the actual slopes of the point stabilizer. These tests eliminate candidates but do not enumerate the remaining actions.

For a square-matrix radical acted on by two special linear factors, the [ordinary fixed-factor inversion is now excluded](manuscripts/0108-ordinary-tensor-idealizers.md) over every odd field in all ranks at least three. This complements, rather than assumes, the earlier matched factor-exchange theorem.

The linked theorems retain their specific canonical-folder, classification, embedding and finite-data hypotheses. Excluding a full multiplication socle is not the same as excluding a canonical left group; classifying a group action is not yet classifying its loop operations.

## Open problems

The main remaining work is to:

- settle the odd-characteristic, socle-containing PSL/PSU branch in even dimensions at least six, and the other symplectic and orthogonal full actions;
- determine operations in the surviving natural alternating/symmetric actions and resolve factor-preserving affine inversion in characteristic two;
- identify the quotient groups, modules and mark sets which pass the radical-positive descent tests, and exhaust the remaining factor-permutation and nonsplit Bruck cases.

The [open-problem board](OPEN_PROBLEMS.md) gives exact assumptions and useful starting points. The historical many-factor symplectic source dispatch still has **unverified global coverage**; its earlier aggregate acceptances were withdrawn. New direct geometric arguments do not retroactively repair that induction.

<a id="research-reference"></a>

## Read and contribute

- [Start here](START_HERE.md): definitions, orientation and reading paths.
- [Results](RESULTS.md) and [claim catalogue](CLAIMS.md): statements, scope and proof links.
- [Complete source index](sources/README.md) and [references](REFERENCES.md): arguments, executable dependencies and literature.
- [Publication record](PUBLICATION-2026-11-17-LATEST.md): synchronized source boundary, corrections and verification limits.
- [Publication history](PUBLICATION_HISTORY.md): earlier checkpoints and the previous detailed overview.

<a id="intrinsic-and-analytic-continuation-2026-11-16"></a>
<a id="sparse-quantum-randomization"></a>
<a id="charged-analytic-transport-and-reconstruction"></a>

## Related Bol-loop research

The following results study broader loop families and applications, not an unrestricted simple-loop classification:

[Graph-native constructions](graph-loops/README.md) · [Decomposition and deletion decks](loop-decomposition/README.md) · [Intrinsic nonisomorphism](INTRINSIC_NONISOMORPHISM.md) · [Analytic families](analytic-2026-11-16/README.md) · [Finite-field counting](analytic-2026-11-16/manuscripts/bol-collective-incidence.md) · [Quantum randomization](analytic-2026-11-16/manuscripts/bol-quantum-randomization.md) · [Charged analytic transport](analytic-transport/README.md)

Graphical deck reconstruction is equivalent to graph reconstruction, not solved. The analytic and quantum results retain their stated family and resource restrictions.

## Conventions

We use the **left Bol identity**:

```math
x\bigl(y(xz)\bigr)=\bigl(x(yx)\bigr)z.
```

“Proper” means non-Moufang; simplicity means normal-subloop simplicity. Passing to the opposite operation preserves simplicity and isomorphism classes but need not give an isomorphic loop. `Mlt(Q)` and `LMlt(Q)` are different groups. Isotopy is not isomorphism; a Bruck isotope is not the same as being Bruck.

<a id="earlier-full-socle-checkpoint-17-november-2026"></a>
<a id="one-milestone-a-simple-bol-loop-outside-two-familiar-classes"></a>

## Provisional research

[Five author proofs and current classification questions](provisional/README.md) are kept separate from the reviewed catalogue. Among them are a proposed **native** universal-subloop construction, an unbounded single-associator order, and an affine-quotient classification. Their finite checks are reproducible; they have not received independent mathematical review.

[Provisional higher-rotation results](odd-prime-pair/README.md#provisional-higher-rotation-results) add two exact-count formulas at the abelian minimum and an obstruction for a restricted nonabelian branch. These proofs also await independent mathematical review.

## Publication scope

This is AI-assisted research, not human-refereed or formally verified mathematics. Review and computation have the exact scopes recorded with each source; novelty is a separate question. The [publication record](PUBLICATION-2026-11-17-LATEST.md) distinguishes preserved proofs, rerun checks and remaining verification gaps.
