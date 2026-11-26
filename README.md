# Public mathematical results

An index of results and proof drafts publicly released in this repository.
Each entry states its scope and verification status; publication does not
by itself imply formal verification or external referee acceptance.

## Prime arrays and lattice reductions

| Result | Exact scope | Sources and verification |
| --- | --- | --- |
| **Sude's First Theorem** | For every positive odd n, exactly the first n² odd primes can be arranged, each once, in an n × n square with prime sums in every row, column and both main diagonals. | [Paper (PDF)](notes/sudes-first-conjecture/paper/sude-prime-sum-squares.pdf), [paper source](notes/sudes-first-conjecture/paper/README.md), [research writeup](notes/sudes-first-conjecture/research-writeup.md), [resolution and proof](notes/sudes-first-conjecture/resolution.md), [complete public replay packet](notes/sudes-first-conjecture/packet/README.md), and [internal nonauthor review](notes/sudes-first-conjecture/proof-source/problems/prime-line-sums/reviews/sude-all-odd-independent-review.md). A conventional computer-assisted theorem with explicit analytic imports and independently reproduced exact checks; no end-to-end formalization or external referee acceptance claimed. |
| **Trimmed coded folding for Euclidean GapCVP** | For each fixed rational 0 < ε < 1/2, a deterministic ordinary reduction from sparse Boolean quadratic satisfiability with source-size bound N has exact gap D^(1/2−ε) and full lattice rank D ≤ N^(1/ε+o(1)). The lattice depends on the instance; this is a rank bound, not the runtime exponent. | [Statement, complete proof packet and finite checks](notes/lattices/trimmed-coded-fold/README.md), with [provenance and verification limits](notes/lattices/trimmed-coded-fold/PROVENANCE.md). A complete mathematical **proof draft**, not formally verified or human-expert-reviewed. |

The [prime-array research index](notes/sudes-first-conjecture/README.md)
also records higher-dimensional and other-field generalizations, each with
its own range and proof status. Those ranges are not enlarged by the
all-odd-order square theorem.

## Normality and constructed numbers

- **[Normal numbers and digit expansions](notes/number-theory/normal-numbers/README.md):** the joint digit-switch lower bound for two coprime bases, [positive lower density of every fixed binary word in the Erdős–Borwein constant](notes/number-theory/normal-numbers/erdos-borwein-positive-word-density/README.md), and the Normal Dovetails construction of normal digit streams. None proves normality of an unchanged traditional constant.

## Diophantine descriptions

- **[Rational points in the middle-third Cantor set](notes/number-theory/cantor-rational-points/README.md):** a proof draft of the Broderick–Fishman–Reich upper bound at ordinary reduced height. The power is sharp, but the new lower bound rules out every fixed power of the logarithm as the remaining factor, including uniformly within Cantor cylinders up to any fixed fraction of logarithmic depth. Includes a [paper (PDF)](notes/number-theory/cantor-rational-points/paper/cantor-rational-points.pdf). Internally cross-checked, not externally refereed.

- **[Integer-polynomial golfing](notes/number-theory/integer-polynomial-golf/README.md):** a complete 1,520-character Python generator for a 3,779-variable integer quartic. Its rational-witness projection defines the integers **conditional on the explicitly retained upstream arithmetic premises**. Includes readable source, proofs, scoped model reviews, reproducible algebraic checks, and a paste-friendly version. Not an independent proof of those premises or a minimality claim.

## Counting and combinatorics

| Result | Exact scope | Sources and verification |
| --- | --- | --- |
| Counting and stability in graph reconstruction | A quadratic upper bound on the number of ordinary-deck parents implies Legitimate Deck is in LWPP. Every sufficiently large graph is within logarithmically many edge edits of a reconstructible graph; with high probability an independent-edge random graph stays reconstructible throughout an adversarial edit ball of radius proportional to $\beta n^2$ when $\beta n/\log n$ tends to infinity. | [Research writeup and full proofs](notes/combinatorics/graph-reconstruction-bounds/README.md), [paper (PDF)](notes/combinatorics/graph-reconstruction-bounds/paper/counting-and-stability.pdf), [paper source](notes/combinatorics/graph-reconstruction-bounds/paper/README.md). These bounds do not settle the Reconstruction Conjecture. |
| Arithmetic progression circulant permanents | An exact, division-free recurrence for M[i,j] = u[i] + v[j] + t·1[j<i], including C[i,j] = A + B((j−i) mod n), in O(n^5) ring operations and O(n^4) stored ring elements. | [Theorem, direct proof and code](notes/combinatorics/ap-circulant-permanent/README.md), [relation to known weighted matching theory](notes/combinatorics/ap-circulant-permanent/PRIOR_ART.md), and [verification scope](notes/combinatorics/ap-circulant-permanent/VERIFICATION.md). No priority, optimality, formal-verification or external-referee claim. |
| Partial Latin square completions as one exact permanent | An explicit matrix over {−1, 0, 1/2, 1} has permanent exactly equal to the labeled completion count. After forced-cell propagation, a nonterminal instance with h holes and t candidates gives order t+2h and exactly 5t+h nonzeros. | [Construction, complete proof and code](notes/combinatorics/latin-completion-permanent/README.md), with [finite checks and review scope](notes/combinatorics/latin-completion-permanent/VERIFICATION.md). A conventional proof with exact-arithmetic tests; no novelty, zero-elimination, optimality, formal-verification or general counting-speedup claim. |
| Exact uniform generation of labeled Latin squares | For every positive order $`n`$, exact uniform sampling in $`\widetilde O(n^{25})`$ expected total bit work. | [Research writeup, paper and reference sampler](notes/combinatorics/exact-latin-square-sampling/README.md). Internally cross-checked proof draft, not externally refereed; the reference code does not implement the revised runtime bound. |

### Exact extremal and additive results

- **[Fifth greedy Bₕ term](notes/combinatorics/greedy-bh-fifth-term/README.md):** the conjectured leading term is h⁴/3, and an exact formula has least eventual quasiperiod six. The all-orders proof includes reproducible computer checks.
- **[Six-vertex paths in P₈-free graphs](notes/combinatorics/six-vertex-paths-in-p8-free-graphs/README.md):** the exact extremal count at every order, with the unique extremal join for n ≥ 11.
- **[XOR Kneser cliques for triples](notes/combinatorics/xor-kneser-k3/README.md):** exact from n = 81, with least threshold 99 for the eventual formula.
- **[Cyclic projective cubes](notes/combinatorics/projective-cube-counterexample/README.md):** explicit mixed-prime examples and an all-orders dimension-four bound. The earlier dimension-five construction is credited.

## Collatz dynamics

- **[Collatz research](notes/number-theory/collatz/README.md):** One explicit density-zero set of changed steps gives convergence from every positive integer. Arbitrarily sparse periodic changes also give convergence to the same cycle, and the minimum fraction needed for uniform descent has a sharp asymptotic bound. The ordinary conjecture is not resolved.

## Discrete geometry

- **[The smallest square that holds 18 unit squares](notes/geometry/unit-square-packing-18/README.md):** The exact side is (7 + √7)/2 with independent rotations and boundary contact allowed. Computer-assisted proof with an exact construction and a full public replay certificate for the lower bound.

## Turing machines and tilings

| Result | Exact scope | Sources and verification |
| --- | --- | --- |
| 236-state binary PA soundness machine | Its full blank-start output satisfies a fixed guarded, addressed finite-game ω-observer exactly when every first-order PA theorem is true in the standard natural numbers. | [Machine, observer and proof guide](turing-machines/pa-soundness-236/README.md), [complete Lean/source packet](turing-machines/pa-soundness-236/formalization/lean/PASoundness/PAtoCompactEndToEndProofTranslation.lean), and [verification limits](turing-machines/pa-soundness-236/VERIFICATION.md). Separate strategies for all finite games; no computability requirement, halting test, or claim that PA proves its own soundness. |
| 285-state binary P versus NP beeper | From a blank tape, emits finitely many designated transition events exactly when P = NP, and infinitely many exactly when P ≠ NP. The machine never halts. | [Machine and Lean-source release](turing-machines/p-equals-np-285/README.md), [interface audit](turing-machines/p-equals-np-285/INTERFACE.md), and [verification status](turing-machines/p-equals-np-285/VERIFICATION.md). Includes the 286-state whole-state companion. Upstream kernel/axiom checks passed as reported; scoped nonauthor automated source review and independent finite replay passed. No complete independent Lean rebuild claimed. |
| 284-state binary NP versus coNP beeper | From a blank tape, emits finitely many designated transition events exactly when NP = coNP, and infinitely many exactly when NP ≠ coNP. The machine never halts. | [Machine and Lean-source release](turing-machines/np-equals-conp/beeper284/README.md), [Lean interface guide](turing-machines/np-equals-conp/beeper284/INTERFACE.md), and [verification status](turing-machines/np-equals-conp/beeper284/VERIFICATION.md). Exact marked-table theorem; the conventional B-exit companion has 285 states. |
| 266-state binary NP versus coNP beeper | The same finite/infinite-event equivalence for a smaller complete blank-start machine. | [Machine and conventional proof](turing-machines/np-equals-conp/beeper266/README.md), [compression guide](turing-machines/np-equals-conp/beeper266/PROOF.md), and [verification status](turing-machines/np-equals-conp/beeper266/VERIFICATION.md). Scoped internal nonauthor model reviews; no table-specific Lean theorem. B-exit companion: 267 states. |
| 12-state binary Collatz evaluator | On each encoded positive input, halts exactly when its ordinary Collatz orbit reaches 1. Universal positive-input termination is equivalent to the ordinary Collatz conjecture. | [Machine and Lean proof](turing-machines/collatz/evaluator12/README.md) |
| 16-state binary Collatz cycle detector | From a blank tape, halts exactly when a nontrivial positive ordinary Collatz cycle exists. | [Machine and Lean proof](turing-machines/collatz/cycle16/README.md) |
| 17-state binary Collatz beeping machine | From a blank tape, beeps infinitely often exactly when every positive Collatz orbit reaches 1. If b is the least counterexample, emits exactly b(b−1)/2 beeps. | [Machine, ordinary mathematical proof and finite checks](turing-machines/collatz/beeping17/README.md) |
| 30 fourteen-sided polygons with recurrence | An unseeded whole-plane tiling with fixed same-root completion recurrence exists exactly when full positive Collatz holds. Ordinary tileability is unconditional. | [Proof, exact geometry and reproducible checks](tilings/collatz-30/README.md) |
| 488 Wang tile types for a seeded half-plane | With seed 487 at the origin of ℤ × ℕ₀, tiles the half-plane exactly when the pinned K215 machine does not halt. The ZFC consequence uses the upstream machine calibration. | [Tile set, ordinary mathematical proof and reproducible checks](tilings/wang-488/README.md) |

**Reproduction note:** The 266-state package’s Python 3.11-or-newer guidance is too broad. On this host, its full checks passed with Python 3.12.14; Python 3.13.5 changed AST output and failed reproduction and a static check. Use Python 3.12 for those commands.

These are correctness reductions. They do not resolve P versus NP, prove the
Collatz conjecture or the consistency of ZFC, and make no minimality or record claim.

See attribution and license status for the [Turing-machine results](turing-machines/ATTRIBUTION.md),
the [488-tile construction](tilings/wang-488/ATTRIBUTION.md),
and the [30-polygon construction](tilings/collatz-30/ATTRIBUTION.md).

## Logic and complexity

- **[Power-of-two counting captures uniform TC⁰](notes/logic/power-of-two-counting/README.md):** On every finite linear order, ordinary truncated multiplication is definable using only order and a unary power-of-two cardinality test nested at most three deep. This gives DLOGTIME-uniform TC⁰ capture on nonempty ordered words. [Paper (PDF)](notes/logic/power-of-two-counting/paper/power-of-two-counting.pdf). Depth one is impossible; depth two remains open.

- **[Unary existential updates for “no adjacent aa”](notes/logic/unary-existential-no-aa/README.md):** a uniform maintaining program with unary auxiliary relations and no built-in arithmetic. This refutes the specific nonmembership prediction, not just a positive-update variant.

## Research notes

- [Theories K: a formal substitution catalogue](notes/set-theory/theories-k-substitution-catalogue.md) (2026-10-23 definitions draft). Precise first-order schemas, with established results distinguished from research reductions and outstanding proof obligations; no new full equivalence is claimed as formally verified.

## Nonassociative algebra

- **[Bol-loop research](notes/finite-simple-bol-loops/README.md):** one workspace for the simple-loop classification, Burnside and Hall–Sylow questions, and graph and analytic applications. The [claim catalogue](notes/finite-simple-bol-loops/CLAIMS.md) links each result to its proof and review scope.

### Further results on loops and quasigroups

- **[Frattini subloops of finite Moufang loops](notes/nonassociative-algebra/moufang-frattini/README.md):** normality and central nilpotence.
- **[Bol and Moufang multiplication-table distance](notes/nonassociative-algebra/bol-moufang-table-distance/README.md):** nonisomorphic left Bol loops at distance n; Moufang isomorphism below n²/20.
- **[Isotopically universal varieties](notes/nonassociative-algebra/isotopically-universal-quasigroup-varieties/README.md):** a universal variety containing no whole loop parastrophe.
