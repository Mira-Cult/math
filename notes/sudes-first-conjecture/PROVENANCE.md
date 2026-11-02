# Provenance and review status

## Scope

This public note presents Sude's First Conjecture, the original qualitative
proof of eventual existence, and the explicit sufficient cutoff
$N_0=2^{2^{40}}$. It is maintained as Mira-Cult research. The theorem for
all odd $n\ge N_0$ is distinguished from the conjecture for every positive
odd order in the [main note](README.md) and [explicit proof](explicit-bound.md).
The unresolved finite range is not claimed to have been checked.

## Original qualitative source revisions

The mathematical source is the prime-line-sums manuscript set in
`Mira-Cult/math-wip` at scientific revision
`4ac266e7c4994a8502eb2a0c57d6b1d3fbd801c5`.
Its recorded scientific tree is
`69bf80823fb4e0ac8e453da9f7fadf2cf9c82434`.

| Public file | Source manuscript in `problems/prime-line-sums/manuscripts/` | Source Git blob |
|---|---|---|
| [proof.md](proof.md) | `eventual_prime_squares.md` | `4196402379f0bffd6ecba5c4c1a347f0a3ac0a24` |
| [controller.md](controller.md) | `reservoir_continuation.md` | `529a50b6c79e3a4aaee107c110d0578b64cfcd04` |
| [prime-targets.md](prime-targets.md) | `analytic_continuation.md`, analytic source contract and A1–A4 | `03fe617eef96571736824237ecf1264a7a813ac3` |

Review status was checked against delivery revision
`1fd32e2c81d422d3e7e0c6ba69934c84ad0a612c` of the source repository,
whose review record identifies that same scientific revision.
These identifiers locate the source history; the public mathematical argument
is contained in this note and its cited primary literature.

## Original qualitative adaptation

The component proofs retain their mathematical hypotheses, constants and
quantifiers. In particular, the controller retains its all-large-scale
quantitative seed argument, depletion and placement bounds, residue repairs
and centered completion. The analytic component retains the complete
fixed-class derivation, including prime powers and bounded filtering costs,
and the exact-total prime-vector lemma uniform in vector length.

Introductions and links have been rewritten for a standalone public note.
Repository workflow material and numerical replay instructions are not part
of this exposition. Mathematical notation is formatted for GitHub Markdown.
The conjecture is stated for all positive odd orders. This original argument
is qualitative; the explicit cutoff is supplied by the supplement below.

One elementary simplification has been added to the synthesis: since
$\mu\le nX$, $X\ge n^2$ and $K\ge n^{2/3}$, its capacity inequality (P3)
already follows for every $n\ge3$ from

$$
\frac{\mu^{3/5}}{KX}\le n^{-13/15}<\frac25.
$$

This removes an unnecessary threshold from that comparison only. It does not
evaluate the original argument's other thresholds. The explicit supplement
uses a separate quantitative construction.

## Original qualitative review boundary

The pinned source reports internal reviews by reviewers other than the
component authors, covering the universal controller, the analytic
prime-target arguments and their synthesis. Those reviews found no remaining
blocking mathematical gap. They are internal mathematical reviews, not
anonymous external peer review or formal proof-assistant verification.

The proof remains open to public scrutiny. Its analytic imports retain their
stated hypotheses. Checking how an imported theorem is used is not a claim
that its entire published proof has been independently reproved here.
The original argument did not evaluate $n_0$. No external acceptance or
novelty claim is asserted for either argument.


## Explicit-cutoff source revisions

The supplement is adapted from scientific revision
`c2118dfad1aeb660d66308dc6a94d6c959f5010c` of the prime-line-sums
manuscript set in `Mira-Cult/math-wip`, with scientific tree
`b62e4be6011e7f9ea0d16c1992529f038e7936bb`.
Review and recovery status was read at delivery revision
`38e1d98cd99eeddfb1f37ad3d140490418e632fc`.
These are provenance identifiers, not inaccessible proof dependencies:
the necessary local arguments are included in this public note, with the
imported classical literature linked in [References](REFERENCES.md).

| Public file | Source manuscript in `problems/prime-line-sums/manuscripts/` | Source Git blob |
|---|---|---|
| [explicit-bound.md](explicit-bound.md) | `explicit_threshold_specialized.md` | `212fa03315e7f769c1a1c6b423f754ec49f327b3` |
| [classical-primes.md](classical-primes.md), mean bounds, E1 and E2 | `effective_pair_supply.md` | `84f1c754a48d276f9ae662516f5813c6c56aca0e` |
| [classical-primes.md](classical-primes.md), S40 interfaces | `classical_interface_specialization.md` | `bf825a1ac5f9de28f6a6628968af38643fec1275` |
| [explicit-controller.md](explicit-controller.md), FC | `explicit_controller.md` | `d8a7c7f83ddb46b5716f43154542ea8e93cdf92a` |
| [explicit-controller.md](explicit-controller.md), PC3 | `explicit_controller_improvement.md` | `71d3013379acf085cfbcfe7804397973afc4756e` |
| [explicit-targets.md](explicit-targets.md) | `explicit_prime_targets.md` | `e9ee67afb4ba70aba454576ed88834b42d11fcf5` |

The source history preserves the corrected earlier numerical checkpoint at
scientific revision `06f214078caad757697a69757e3e10054d86ee1d`, delivered
at `511c7f466d789467f5d532a0eca73c51709f77f2`. The current supplement
uses the directly specialized progression estimates, not the earlier larger
starting points.

## Explicit-cutoff adaptation and review boundary

The public supplement keeps the exact pool, repeating-line-sum permission,
all numerical hypotheses and every uniform-tail argument. It includes the
full finite controller, its numerical specialization, the exact-total target
lemma, the elementary prime-pair matching, the pool-mean proof, the corrected
primitive-character smoothing argument, and both specialized progression
proofs. Elementary grid and graph arguments are reproduced inline. Introductions,
links and mathematical notation have been edited for a standalone public note.
The Git blob identifiers above refer to the source manuscripts, not to the
adapted public Markdown bytes.

The source's internal review record covers the analytic supplies, FC and PC3,
the target lemma, and their full composition. The final specialization received
a fresh nonauthor audit covering both progression interfaces and the complete
composition. A separate composition review was by the analytic specialization's
author; it is not counted as independent review of that author's analytic work.

An earlier review found a mismatch between primitive and imprimitive zero-set
normalizations in the smoothing argument. The corrected E2 proof retained here
passes to primitive inducing characters and explicitly subtracts the omitted
prime-power terms. The correction fits the stated remainder bound and changes
no subsequent numerical constant. The earlier objection and repair remain part
of the source history rather than being treated as an arithmetic-only issue.

The source record also reports exact integer/rational checks of the numerical
interfaces, endpoint bounds, persistence conditions and source bindings. Those
programs are not distributed as a standalone public certificate here; this
exposition does not claim that a private replay command is a publicly runnable
proof. The mathematical inequalities and their whole-tail justifications are
included directly. Arithmetic checks do not prove the imported analytic results
or replace conventional proof review.

The classical imports retain their published hypotheses and computational
inputs. In particular, the source review used publisher-indexed McCurley text;
direct access to the original publisher PDF was unavailable during that review.
No independent page-by-page verification of that PDF is claimed. The exact
formulas and locators used are disclosed in [References](REFERENCES.md).

The result is therefore presented as a **proposed unconditional conventional
proof with internal nonauthor review**, not formal verification, external peer
acceptance, or a practical construction. It does not settle all odd orders
below $2^{2^{40}}$.
