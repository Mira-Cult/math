# Verification and provenance

This is conventional mathematical research. Independent checks below were
conducted by OpenAI models, not by human referees or proof assistants.
Mira Cult directed the research. OpenAI models assisted with proof discovery,
exposition, and separate mathematical review. Exact model versions are not
recorded for all contributions. No priority claim is made.

The identifiers in this table pin the research sources before public notation,
formatting, and navigation edits. Permanent IDs at left are public catalogue
IDs, not numbers assigned to the original research.

| Claim | Research sources and check scope |
| --- | --- |
| 0127, minimum and census | `1de454fb` and the independent [assembly](reviews/first-degree-odd-prime-pair-assembly.md) at `1753f6dc`. Separately checked: the faithful signed group and physical stabilizer, the axial benchmark and existence, the extraspecial reduction, and the exceptional even-$`f`$ census and arithmetic phase counts. |
| 0128, gap | `203d66d9` (central sign-fixed Frattini group), `233e57e7` (axial lift exclusion), `eab423e6` ($`p\nmid f`$ mixed case), and `e35522a0` ($`p\mid f`$, readable revision `be997836`). Independently checked under the cited signed-group and first-degree inputs, including the characteristic-three budget and the physical lift of order $`p^2`$. |
| 0129, ternary construction and restricted census | Existence at `4330b2c7` was independently checked for inversion, transversal size and avoidance, generation, core-freeness, and all strict normal cuts. The separate `f9743027` census audit checked the elementary-core reduction, signed equivalence and Burnside evaluation. One independent exact check solved 234 fixed-point systems over the field of order three for $`f/9=1,\dots,12`$; this finite check does not replace the general proof. |
| 0130, higher rotation groups | Source `d30641cc` was read independently for the all-core, $`p\mid f`$ rotation-sensitive bound. The elementary purely axial obstruction (§2 of `b16e57d1`, clarified at `6faf079e`) passed separate mathematical review under the canonical two-axis hypotheses. The independent proof reads at `a636051a` and `ea7017d5` checked, respectively, the mixed weight cost and the additional axial necessity leading to the sum. They claim neither sharpness nor general higher-top existence. |

The supporting [fixed-Frattini manuscript](manuscripts/third-degree-p-square-top-fixed-frattini.md)
at `949c4506` is not certified here as a separate result for non-elementary
cores. The independent ternary census covers the reduction in its
elementary-core scope. The [extraspecial residue addendum](manuscripts/first-prime-pair-extraspecial-residue.md)
is an auxiliary author proof, not a separately reviewed classification.

## Reproducible arithmetic

Run with Python 3 from this subworkspace. These are finite algebra checks, not
searches over entire multiplication tables or a substitute for proof.

```sh
python3 code/verify_ternary_top_nine_chart_count.py
python3 code/verify_first_degree_two_sheet_orbits.py
```


## Fixed-Frattini proofs

| Public claim | Scientific source and scoped proof review |
| --- | --- |
| 0131 | `e82fd017`: exact quotient mark multiplicity and physical dimension calculation; the projected lift argument is distinguished from an actual collision. The nonabelian single-packet exclusion uses the central commutator and an invariant nondegenerate contraction. |
| 0132 | `b66d0fc5`, `47991cbd`, `0fd97ea1`: rank and radical averaging, exponent-p reduction, core-free exclusion of moving radical packets, complete even-degree multiplicity-one axial exclusion, and odd-degree reciprocal count. |
| 0133 | `c3487774`, `e0c0257a`: rounded Witt bound using whole-first-axis isotropy, the top-zero signed conjugacy and central bracket, and the nonzero-top affine phase coset. The radical-quotient simplification requires fixed-point lifting. |

These were scoped nonauthor mathematical reads by OpenAI models, not human
referee reports or formal verification. The cited revisions are provenance
identifiers; the proof dependencies are included on the public pages.
