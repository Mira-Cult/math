# Selected results and construction drafts

This catalogue is a selected snapshot, not a complete inventory of the active
research branch. The source snapshot is `27d51e6a23363d6c0ae74b2f6f752db9bb5e5847`
(15 November 2026). Novelty is not established by inclusion here.

## A finite simple proper Bol loop outside both historical classes

The [specialized existence proof](simple-existence-proof.md) gives a direct route.
The [original class-two framework](packet/manuscripts/odd-class-two-classification.md)
is also preserved, with its broader review limits distinguished.

The [rigid-center manuscript](packet/manuscripts/odd-rigid-center-nongloop.md)
constructs a finite simple proper **left** Bol loop of order

\[
3^{75}19^3
\]

which is not a G-loop and is not isotopic to a Bruck loop. The non-G-loop argument
exhibits a principal isotope and excludes an isomorphism using the precise
isomorphism relation, rather than merely showing that a convenient family of
coordinate changes fails. The obstruction distinguishes alternating matrix parts
with determinants 1 and 0 over the field of three elements.

This addresses the existence question in Nagy's *Some remarks on simple Bol
loops* (2008), §6 Problem 1, **if the argument and its stated interfaces are
accepted**. The question was still reported unresolved in a 2021 source. A bounded
literature search is not a priority certification, and this example is not claimed
to be sporadic merely because its order is large.

The current independent model audit found no defect in the construction and the
specific folder, inversion, strict-defect, class-two construction/isomorphism,
principal-isotope and Bruck-isotopy interfaces used. It did not audit the full
class-two exhaustion theorem or the global classification. The arithmetic
certificate was rerun, and an independently written checker compared 10,000
fixed-seed BCH-section products against the displayed multiplication formula.
Neither check constructs the huge loop or replaces the universal proof.

See [packet scope](packet/README.md) before using the supplementary sources.

## Further selected construction and classification drafts

The following are selected contributions from the same snapshot. Their local
arguments received scoped model review; supporting source files are included.
That review is not a complete new audit of every imported or supplementary theorem.
The manuscript statements retain their exact hypotheses and original review scope.

| Development | Exact mathematical value | What it does not establish |
| --- | --- | --- |
| [Unbounded derived nilpotency class](packet/manuscripts/odd-unbounded-derived-class.md) | For every c≥2, constructs odd simple proper loops whose canonical `LMlt` derived subgroup is nilpotent of class c. | An exhaustive description of all higher-class envelopes. |
| [Unbounded derived length](packet/manuscripts/odd-unbounded-derived-length.md) | For every n≥4, constructs odd simple proper G-loops with canonical group derived length 1+⌈log₂n⌉. | A uniform bound or a complete solvable-envelope classification. |
| [Unbounded Fitting height](packet/manuscripts/odd-unbounded-fitting-height.md) | Constructs odd simple proper loops with canonical group Fitting height h+3 for every h≥0. | The impossibility of any structural classification. |
| [Matrix-pair embedding](packet/manuscripts/odd-matrix-pair-embedding.md) | Encodes simultaneous similarity of arbitrary matrix pairs as loop isomorphism in a specified odd simple proper G-loop family. | A polynomial-size multiplication table, complexity-class hardness theorem, or all-loop classification. |
| [Single-root affine classification](packet/manuscripts/nonbruck-single-root-classification.md) | Gives exact data for regular affine subgroups whose nontrivial linear projection lies in a single root group, with stated loop-interface hypotheses. | Exhaustion of other affine projection types or all Bol loops. |
| [Monolithic Heisenberg and higher-defect constructions](packet/manuscripts/odd-monolithic-higher-defect-isomorphism.md) | Supplies explicit admissibility, constructions and within-family isomorphism data, including positive and negative arithmetic controls. | That displayed counts exhaust every loop of the corresponding order. |

Additional [noncentral-center](packet/manuscripts/odd-noncentral-jordan-center-family.md)
and [fixed-shadow](packet/manuscripts/odd-fixed-shadow-simple-example.md) constructions delimit proposed
normal forms. The guiding lesson is structural: a viable classification must
accommodate more than one simple quotient pattern or one bounded group invariant.
