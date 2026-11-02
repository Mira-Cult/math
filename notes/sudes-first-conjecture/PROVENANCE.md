# Provenance and review status

## Scope

This public note preserves three separate manuscripts: the original qualitative proof of eventual existence, the initial public explicit cutoff $`2^{2^{40}}`$, and the optimized explicit cutoff $`2^{4320}`$. Each applies to the exact first $`n^2`$ odd primes and to every odd order in its asserted tail. None proves the conjecture for every positive odd order or claims to have checked the entire remaining finite range. See the [manuscript index](README.md).

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
$`\mu\le nX`$, $`X\ge n^2`$ and $`K\ge n^{2/3}`$, its capacity inequality (P3)
already follows for every $`n\ge3`$ from



```math
\frac{\mu^{3/5}}{KX}\le n^{-13/15}\lt \frac25.
```



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
The original argument did not evaluate $`n_0`$. No external acceptance or
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
at `511c7f466d789467f5d532a0eca73c51709f77f2`. The initial explicit supplement
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
below $`2^{2^{40}}`$.



## Optimized bound

The third manuscript gives the proposed unconditional cutoff $`2^{4320}`$ for the same complete odd-order tail and exact prime pool. Its frozen scientific source is revision `f519b7fd796393cd6ab202f6790fe1824e6fc22f` of the research repository, in `problems/prime-line-sums/`. The final review delivery is revision `b776784e3cffc3aeeb3c3c6886516c3337a16bd1`. The first two public manuscripts remain preserved. The new argument does not merely substitute a smaller number into their statements.

### Public proof and editorial transformations

[The optimized composition](optimized-bound.md) and the manuscripts in [its supporting directory](optimized/) reproduce the active classical proof chain. Dependencies on the earlier finite controller, original target lemma, and corrected primitive-character explicit formula link to the already public manuscripts. The mathematical argument is readable without access to the research repository.

The public adaptation changes display and inline mathematics to GitHub-safe syntax, replaces equation tags by text labels and literal comparison signs by equivalent TeX macros, rewrites links to public counterparts, removes internal workflow instructions and inactive future-work discussion, and separates executable-recovery claims from the mathematical exposition. It does not change the asserted theorem or its proof inequalities. A token comparison checked all 292 retained display formulas and 108 inline LaTeX expressions against the frozen source, ignoring whitespace, equivalent comparison macros, and equation-label presentation. The only omitted display formulas were two in a removed discussion of an unsupported smaller candidate. The [source map](optimized/source-map.json) records the input and public-output SHA-256 hashes for each adapted manuscript. The exact-byte source recovery and these formatted manuscripts are different artifacts; the original manifests must not be run against edited exposition bytes.

### Final source reviews

The final delivery contains two reports on the exact scientific revision:

- **Fresh nonauthor mathematical review.** The reviewer did not author or edit the producers, chosen profiles, composition, or verifier. The report found no blocking issue after examining the active analytic, graph, controller, seed/target, composition, and whole-tail arguments, including the relevant primary Rosser–Schoenfeld, BMOR, and McCurley statements. It independently reconstructed and replayed the complete 81-file recovery. A separately implemented standard-library rational oracle, importing no producer module, passed 57 named checks and finite adversarial controls. This is internal conventional review, not an external referee report or a kernel proof.
- **Scoped composition cross-review.** The analytic component author checked the separately authored final composition, scale translations, manifests, and certificate wrapper, and independently replayed the same recovery. That report found no blocking issue within its scope. It expressly does not count as nonauthor review of the analytic derivations, controller architecture, target refinements, or joint parameter selection in which that reviewer participated.

Both source reviewers obtained deterministic replay-output SHA-256 `de3926189b8383dc73f128ff27cf982aa48fa487338ce1a4e6be2cadb24bc361`. A further publication-side recovery and replay reproduced the same result. The final reports make their authorship exclusions explicit; their conclusions are not silently extended to later scientific changes.

### Independent publication checks

A separate internal recovery reconstructed all **81** required source files from the frozen revision and checked all **80** dependency hashes. The complete certificate passed: **55** final composition checks, **6** top-level component replays including the historical **16**-component campaign, **20** final malformed-manifest, parameter, and preceding-bound controls, and **401** physical file attacks rejected as intended. The final manifest SHA-256 was `66510e1283506b5eadafeaa5c06ae844ae79ffd7ad65fd1b4da59f669765b2dc`.

The arithmetic checks certify the declared finite inequalities, source integrity, and negative controls. They do not prove the imported analytic results, turn handwritten arguments into kernel proofs, or construct an explicitly listed square of order $`2^{4320}`$. Mathematical source review of the final analytic, finite-controller, target, and whole-tail composition is recorded separately from this replay. Component collaborators are not counted as independent reviewers of their own contributions. Publication review is internal, not external peer acceptance.

The new classical deductions use Rosser–Schoenfeld for index and pool-mean bounds, Bennett–Martin–O'Bryant–Rechnitzer for explicit zero-counting and exceptional-zero estimates, and McCurley's parameterized explicit-formula and zero-sum calculations. In particular, the extended source domain is proved from the parameterized formulas; a published lemma is not simply invoked outside its printed domain. The corrected primitive/imprimitive character normalization and omitted Euler-factor prime-power allowances are retained.

No claim of optimality, a proof for the full finite remaining range, or a practical construction at this scale is made.



## Full signed-line cube

Manuscript IV gives a proposed unconditional conventional proof that, for every sufficiently large odd n, exactly the first n³ odd primes can be placed once each in a cube with prime sums on all 3n²+6n+4 full signed-coordinate lines. The threshold is ineffective and unevaluated. The result includes every axis line, both diagonals in every coordinate-parallel square slice, and the four body diagonals. It does not require a square-section sum to be prime.

### Sources and complete public dependency chain

The four new mathematical sources were frozen at research revision `a2445962ec6e06b2a893980fb7a183057eb9bcee`: `signed_cube.md`, `signed_incidence.md`, `signed_targets.md`, and `signed_trades.md`. The final delivery and review revision is `cdb7879e358f93afa54b685027a27692d22635a9`. The separately reviewed full-matrix integer-kernel certificates were frozen at `f44ac4d78246d8190f653fdbc3ee18525f6c5cc1`. The axis-controller and target baseline was preserved from `aba3397991165103c2bebca3a898a4b30d79fcb2`.

The public [composition](prime-cube.md) and [six supporting manuscripts](cube/README.md) include the complete active mathematical chain: full integer compatibility, signed physical cuboid trades, prime targets and residue routing, the baseline triangular axis controller, symmetric exact-total targets, and bounded tensor-expander coefficients. The [finite target-list lemma](explicit-targets.md) and [degree-64 graph construction](controller.md#f-independent-row-and-column-controls) are reused from the already public square proof. The latter retains the expansion-eight capacity used by the cube argument; it is not replaced by the optimized square proof's different graph constants.

The named non-elementary prime-distribution input is the short-interval progression consequence in Section 1.2, printed page 3, of [Thorner–Zaman, arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2). The manuscripts specify its interval lengths, logarithmic modulus range, uniformity, and ineffective threshold. No growing-complexity prime-pattern theorem is substituted for this input.

Public exposition changes notation and links for readability, omits internal workflow instructions and unrelated investigations, and uses GitHub-safe math delimiters, equivalent comparison and roman-operator macros, and text equation labels. The incidence appendix retains its complete active axis-image, integer-rounding, and tensor-expander proofs; unrelated later sections on other constraint systems are not needed here. Executable instructions are replaced by the verification description below so that the exposition does not claim private programs are publicly runnable. The [source map](cube/source-map.json) binds source and public manuscript hashes. These edited exposition bytes are not the exact-byte scientific recovery.

### Review and finite checks

Four fresh internal nonauthor reviewers examined the integer, geometric, analytic, and end-to-end composition aspects of the frozen sources. Their reports identify authorship boundaries, exact revisions, inspected arguments, finite tests, and exclusions. They found no blocking defect in their stated scopes. Component collaborators' preliminary cross-checks were not substituted for these fresh reviews. A further publication-side read of the new composition and its dependencies found no concrete defect within its bounded scope.

The publication-side replay used Python 3.12.14 and exact source/input bytes matching the recorded bindings. It reproduced:

- Exact-pool prime cubes at n = 1, 3, and 5, with respectively 1, 49, and 109 required prime line sums; 18 corrupted certificates were rejected.
- An order-19 physical fixture using all 6,859 prescribed primes, 44 available switches and four selected stages, changing exactly one signed line while preserving all others. This is a trade certificate, not a claim that every line in that fixture is prime.
- Joint support fixtures at orders 31 and 51, with no old-control body hits and maximum old face loads 8 and 14. Four corrupted geometries and three invalid exponent choices were rejected; eight positive asymptotic exponent margins were checked.

The delivered source also contains complete integer-image and kernel certificates at n = 3 and 5, checked by independently reconstructed line matrices and unimodular transformations, and finite compatible-target certificates. These additional source review records were inspected; they are not described as a second publication-side replay of every test. The order-five torsion conditions and the order-three obstruction to adding a diagonal-square prime-sum requirement remain part of the mathematical account. They do not contradict the positive full-line examples.

Finite checks do not prove the asymptotic analytic supplies, uniform packing, or the full eventual theorem. The proofs of those statements are the conventional arguments in the linked manuscripts. The publication review did not independently reprove the external analytic theorems or their computational inputs, and no end-to-end kernel formalization is claimed. The source's final remote CI was skipped rather than passed; no full-repository CI pass is asserted here.

This publication makes no literature-priority, external peer-acceptance, efficient-construction, evaluated-cutoff, or growing-dimension arrangement claim. The three square manuscripts remain unchanged.


## Explicit prime cube

Manuscript V, [explicit-prime-cube.md](explicit-prime-cube.md), adds the
explicit full signed-line cube bound $`2^{61750}`$. It preserves Manuscripts
I–IV and the square bound $`2^{4320}`$. It asserts existence for **every odd
order at or above the stated bound**, with exactly the initial odd-prime
pool, all full signed lines, and no square-section primality assumption.

### Source and earlier checkpoint

- Optimized scientific snapshot: `c6880d03d0025b44d3c5a56bec9e80a11d38e45b`.
- Final delivery and independent internal review records: `117c33de62d0dc24730e9e49b7991b67ef3eed5c`.
- Earlier successful scientific checkpoint: `ad17fce4ad0605a70fdc4e04b7c842622f9f587e`, with bound $`2^{250226}`$. It remains a historical fallback, not the current cutoff. A redundant growth-deletion row originally missed a factor two; a stronger midpoint condition already implied the required inequality. The corrected replay preserves that first theorem. The final phased proof uses its own correct early invoice.
- Qualitative cube science: `a2445962ec6e06b2a893980fb7a183057eb9bcee`, already represented by Manuscript IV.
- Imported optimized-square science: `f519b7fd796393cd6ab202f6790fe1824e6fc22f`; review delivery `b776784e3cffc3aeeb3c3c6886516c3337a16bd1`.

The readable edition publishes the complete main composition and six
supporting manuscripts under [cube-explicit](cube-explicit/README.md).
Existing public geometric and analytic proofs supply its explicitly linked
imports. In particular the six reused optimized-square manuscript sources
were compared with the recovered imported copies: their contents agree
apart from trailing whitespace. The corrected E2 import has raw SHA-256
`70b1e235b91885882afedd2e206df8f59e0064bf8923a6d9d3937ebe1a2a7c4d`.
The [source map](cube-explicit/source-map.json) records source and public
hashes. Math rendering changes replace delimiters, relation symbols,
operator formatting and equation labels only; retained formula tokens were
checked against their source excerpts. Recovery-only execution instructions
and attribution bookkeeping are replaced by this record. Inactive analytic
alternatives are not part of this publication's proof chain.

### Fresh verification and review

The recovered self-contained archive has SHA-256
`09637abd8e451b8d3bf3625905c59f5a35e06efc7b252260482295b35461a79c`.
A fresh offline replay checked all 197 member hashes and completed all 29
recorded commands. This includes the initial checkpoint and final optimized
composition, independent reflected-supply and analytic arithmetic oracles,
and delivery recovery checks. Its final composition binds 73 scientific
sources/inputs, checks 30 controller/supply interfaces, seven local analytic
request types, nine target comparisons, and 38 relevant rejection controls.
The delivery checker additionally passed 25 packaging negative controls and
two synthetic dispatch checks. These are finite arithmetic and recovery
results, not an enumeration of a cube at this astronomical order.

The exact cutoff representation was independently checked to equal
$`2^{61750}`$. All-tail justification is mathematical: pointwise ceiling
bounds and nonnegative Laurent envelopes, together with separate analytic
and target derivative guards. It is not inferred by sampling later orders.
The predecessor $`61749`$ fails the selected sufficient envelope, not the
conjecture; no optimality claim is made.

A separate publication-scope review read the complete composition and its
changed analytic, target, packing and reflected-allocation interfaces and
found no blocking defect. The reviewer did not author those components.
That pass did not independently reprove all classical analytic imports,
the complete tensor proof, or signed-incidence proof. Earlier source-level
internal reviews and the fresh replay have their own stated boundaries.
This is a conventional mathematical proof with internal review: **not** an
end-to-end kernel-checked theorem, external peer acceptance, or a claim that
remote CI passed. The recorded remote CI run was skipped. Public exposition
hashes differ from the research archive after formatting and link editing;
its original byte-binding manifest is not claimed to verify these edited
files. The executable recovery archive is distinct from this proof edition.
