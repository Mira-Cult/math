# Source map and final import ledger

This document and `import-map.json` record the **complete, final import ledger**
for `Sude.sude_first_theorem` and `Sude.sude_first_theorem_values` in
`Sude/AllOddTheorem.lean` (as well as `Sude.tail_hasSquare : Sude.TailObligation`).

Completion is a **Lean-checked proof relative to the 16 explicitly listed exempt
inputs below** (`Sude.FiniteWitness` for positive odd `n < 2000`, plus 15
verbatim published analytic inequalities from Rosser–Schoenfeld 1962,
Bennett–Martin–O'Bryant–Rechnitzer 2018, and Montgomery–Vaughan 1973). It is
**not** an assumption-free end-to-end kernel proof. No global Lean `axiom`,
`sorry`, `admit`, `native_decide`, `TailObligation` premise, route/controller
premise, physical-construction premise, target-prime premise, or internal
numerical certificate premise appears in the final theorem.

## Complete exempt hypothesis table for `Sude.sude_first_theorem`

| # | Lean hypothesis (`Prop`) | File & line | Source & exact locator | Mathematical statement & domain |
|---|---|---|---|---|
| 1 | `Sude.FiniteWitness` | `Sude/Statement.lean:45` | Exempt finite family (`FR1`–`FR5`, `cutoff2_finite_remainder_squares.md`) | `∀ n, 0 < n → Odd n → n < 2000 → Sude.HasSquare n` (the 1,000 positive odd orders `< 2000`; `n = 1` is also proved unconditionally in `Sude.square_one`). |
| 2 | `Sude.RSPrimeCountLowerSharp` | `Sude/RSPrimeCountImports.lean:56` | Rosser–Schoenfeld (1962), Theorem 2, `(3.3)`, p. 69 | `∀ x : ℝ, 67 ≤ x → x / (Real.log x - 1/2) < primeCountReal x`. |
| 3 | `Sude.RSPrimeCountUpperSharp` | `Sude/RSPrimeCountImports.lean:61` | Rosser–Schoenfeld (1962), Theorem 2, `(3.4)`, p. 69 | `∀ x : ℝ, Real.exp (3/2) < x → primeCountReal x < x / (Real.log x - 3/2)`. |
| 4 | `Sude.RSPrimeCountLower` | `Sude/RSPrimeCountImports.lean:66` | Rosser–Schoenfeld (1962), Theorem 2 Cor. 1, `(3.5)`, p. 69 | `∀ x : ℝ, 17 ≤ x → x / Real.log x < primeCountReal x`. |
| 5 | `Sude.RSPrimeCountUpper` | `Sude/RSPrimeCountImports.lean:71` | Rosser–Schoenfeld (1962), Theorem 2 Cor. 1, `(3.6)`, p. 69 | `∀ x : ℝ, 1 < x → primeCountReal x < (62753 / 50000) * x / Real.log x` (`1.25506 = 62753/50000`). |
| 6 | `Sude.RSIndexLowerSharp` | `Sude/FWSharpIndex.lean:10` | Rosser–Schoenfeld (1962), Theorem 3, `(3.10)`, p. 69 | `∀ j : ℕ, 2 ≤ j → j * (Real.log j + Real.log (Real.log j) - 3/2) < primeOneBased j`. |
| 7 | `Sude.RSIndexUpperSharp` | `Sude/PrimeIndex.lean:39` | Rosser–Schoenfeld (1962), Theorem 3, `(3.11)`, p. 69 | `∀ j : ℕ, 20 ≤ j → primeOneBased j < j * (Real.log j + Real.log (Real.log j) - 1/2)`. |
| 8 | `Sude.RSIndexLower` | `Sude/PrimeIndex.lean:43` | Rosser–Schoenfeld (1962), Theorem 3 Cor., `(3.12)`, p. 69 | `∀ j : ℕ, 1 ≤ j → j * Real.log j < primeOneBased j`. |
| 9 | `Sude.RSIndexUpper` | `Sude/PrimeIndex.lean:46` | Rosser–Schoenfeld (1962), Theorem 3 Cor., `(3.13)`, p. 69 | `∀ j : ℕ, 6 ≤ j → primeOneBased j < j * (Real.log j + Real.log (Real.log j))`. |
| 10 | `Sude.RSThetaUpper` | `Sude/BMORExplicitFormulaImports.lean:56` | Rosser–Schoenfeld (1962), Theorem 4, `(3.15)`, p. 70 | `∀ t : ℝ, 1 < t → thetaAP t 1 0 < t + t / (2 * Real.log t)`. |
| 11 | `Sude.BMORFiniteTheta` | `Sude/BMORFinite.lean:68` | BMOR (2018), Theorem 1.9 theta conjunct & `(1.18)`, pp. 434–435 | `∀ q a x y, 1 ≤ q → q ≤ 10^5 → Nat.Coprime q a.natAbs → 1 ≤ y → y ≤ x → x ≤ bmorLimit q → \|thetaAP y q a - y / φ(q)\| ≤ (259/125) * √x`. |
| 12 | `Sude.BMORProp2_1` | `Sude/BMORPublishedExplicitFormula.lean:644` | BMOR (2018), Proposition 2.1, `(2.3)`–`(2.7)`, pp. 438–439 | Verbatim smoothed explicit formula for `chebyshevPsiAP x q a` in terms of `bmorU`, `bmorV`, and `bmorW` for `q ≥ 1`, `gcd(q,a)=1`, `x > 2`, `H ≥ 1`, `m ≥ 1`, `0 < δ < (x-2)/(m*x)`, under `GRH(1)`. |
| 13 | `Sude.BMORProp2_5` | `Sude/BMORPublishedExplicitFormula.lean:655` | BMOR (2018), Proposition 2.5, `(2.10)`, p. 441 | `∀ q [NeZero q] χ (T : ℝ), 1 ≤ T → \|bmorZeroCount χ T - (T/π) * log(χ.conductor * T / (2*π*e))\| < 0.399 * log(χ.conductor * T) + 5.338`. |
| 14 | `Sude.BMORProp2_7` | `Sude/BMORPublishedExplicitFormula.lean:664` | BMOR (2018), Definition 2.6 & Proposition 2.7, p. 441 | Every primitive Dirichlet character `χ` of conductor `d ≤ 100000` satisfies `bmorSatisfiesGRH χ (bmorVerifiedHeight d)` (`30610046000` at `d=1`, `10^8/d` for `1 < d ≤ 100000`). |
| 15 | `Sude.BMORProp4_34` | `Sude/BMORPublishedExplicitFormula.lean:673` | BMOR (2018), Definition 3.1 (p. 451) & Proposition 4.34, pp. 478–479 | For `1 ≤ q ≤ 100000` and any critical-strip zero `ρ` of `L(s, χ)`, either `\|Im ρ\| ≤ 10^8/q` and `Re ρ = 1/2`, or `\|Im ρ\| > 10^8/q` and `Re ρ ≤ 1 - 1 / (5.6 * log(χ.conductor * \|Im ρ\|))`. |
| 16 | `Sude.MVBrunTitchmarsh` | `Sude/MontgomeryVaughan.lean:12` | Montgomery–Vaughan (1973), Theorem 2, `(1.10)`, p. 121 | `∀ x y > 0, ∀ k a > 0, Nat.Coprime k a → k < y → (apInterval x (x+y) k a).card < 2 * y / (φ(k) * log(y/k))`. |

## Unused legacy BMOR modulus-4 prime-count hypothesis

The proposition `Sude.BMORFinitePiFour` (`Sude/BMORFinitePiFour.lean:36`) is
**NOT used** by `Sude.sude_first_theorem`, `Sude.sude_first_theorem_values`, or
`Sude.tail_hasSquare`. (While `Sude/BMORFinitePiFour.lean` is imported for the
benign definitions `liFromTwo` and `oddPrimeCountReal`, the hypothesis
`BMORFinitePiFour` itself is retained solely as a legacy declaration from the
earlier BMOR Theorem 1.9 prime-count endpoint review; see
[source review](RESEARCH_NOTES.md#source-review-bmor-prime-count-endpoint).)
All prime-progression and pool-mean bounds used in the completed formalization
are proved in Lean from `BMORFiniteTheta`, `BMORProp2_1`, `BMORProp2_5`,
`BMORProp2_7`, `BMORProp4_34`, and the Rosser–Schoenfeld (1962) inputs above.
Similarly, McCurley (1984) is **not imported**: imprimitive-to-primitive
critical-strip zero invariance (`Sude.bmorZeroMult_eq_primitive`), functional
equation symmetry (`Sude.bmorZeroMult_one_sub_star`), and finite Stieltjes
summation by parts are proved directly in Lean in
`Sude/BMORPublishedExplicitFormula.lean` using Mathlib's `DirichletCharacter`
and `LFunction` library.

## Source identity and normalization summary

- **Statement and pool (`Sude/Statement.lean`)**: `oddPrime i = Nat.nth Nat.Prime (i + 1)`
  (`oddPrime 0 = 3`); `pool n` is the range of `oddPrime` over `Fin (n * n)`;
  `HasSquare n` asserts an equivalence `Cell n ≃ Fin (n * n)` whose `rowSum`,
  `columnSum`, `mainSum`, and `antiSum` (via `Fin.rev`) are all prime;
  `Sude.hasSquare_iff_values` proves equivalence with `∃ b : Cell n ≃ pool n, ValuesValid b`.
- **Prime counting and indexing (`Sude/PrimeIndex.lean`, `Sude/RSPrimeCountImports.lean`)**:
  `primeOneBased j = Nat.nth Nat.Prime (j - 1)` (`p_1 = 2`, `p_2 = 3`);
  `poolMaximum n = Nat.nth Nat.Prime (n * n) = p_{n^2 + 1}`;
  `primeCountReal x` counts primes `p ≤ x` via `(Finset.range (⌊x⌋₊ + 1)).filter Nat.Prime`.
- **Chebyshev functions and explicit formula (`Sude/BMORFinite.lean`, `Sude/BMORPublishedExplicitFormula.lean`)**:
  `thetaAP x q a` sums `Real.log p` over primes `p ≤ x` with `p ≡ a (mod q)`;
  `chebyshevPsiAP x q a` sums `ArithmeticFunction.vonMangoldt n` over `1 ≤ n ≤ x`
  with `n ≡ a (mod q)` and is proved equal to `psiAP x q a` for `x ≥ 2`
  (`Sude.chebyshevPsiAP_eq_psiAP`); `bmorIsCriticalZero χ ρ` restricts to
  `0 < Re ρ < 1` so Euler factors at `Re ρ = 0` never vanish; `bmorZeroMult`
  uses `analyticOrderNatAt`.
- **Packet provenance**: Public archive `resolution-packet.zip` (SHA-256
  `9f7580594e535deb32421def057438e862db7b6c1bb140c8929c21f7def3a650`),
  scientific revision `67647907ad0693631f42c169df61cbe46a13a3ff`, PR base
  `965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc`, compressed `FiniteWitness` archive
  SHA-256 `5f8be996b548afac76e276088da5a094e3ff4375075ecea14aec77c71522b27c`
  (provenance hash only; `FiniteWitness` is retained as an explicit hypothesis).

## Closed tail band dispatch (`Sude/AllOddTheorem.lean`)

Rather than eleven separate conditional controllers, `Sude.tail_hasSquare`
partitions all odd `n ≥ 2001` into three exhaustive kernel-checked bands, each
derived solely from subsets of the 15 published analytic hypotheses above
(via `Sude.bmorExplicitFormulaImports_of_published` for explicit-formula supplies):

| Odd `n` range | Lean theorem & module | Internal certificates / analytic regime | Status |
|---|---|---|---|
| `1 ≤ n ≤ 1999` | `Sude.FiniteWitness` (`Sude/Statement.lean`) | Exempt small-order finite family (`n = 1` also proved as `Sude.square_one`) | Exempt hypothesis |
| `2001 ≤ n ≤ 19483` | `Sude.fc2k_hasSquare` (`Sude/FC2KBandTheorem.lean`) | Kernel-checked 8,742-row Lucas FTT target table (`FastFTT`), FPF prefix sieves, BMOR/RS62 T75 analytic supply, DQ/RF central completion, expander routing | Proved in Lean |
| `19485 ≤ n ≤ 35733` | `Sude.fw_and_ew_hasSquare` (`Sude/FWFirstBandTheorem.lean`) | Kernel-checked 3,650,551-pair twin-prime pool (`FastTwinFullPool`), MV73 + BMOR + RS62 bridge/wide/growth, projected CY + spare diagonal balance | Proved in Lean |
| `n ≥ 35735` (all odd) | `Sude.upper_tail_hasSquare` (`Sude/UpperTailTheorem.lean`) | Unified all-scale construction: MV73 + BMOR/RS62 two-phase prefix growth, dyadic bridge, wide blocks, DQ/RF completion, expander routing, mod-6 target primes | Proved in Lean |

---

> **Historical module notes:** The sections below document lower-level component
> modules in the order they were originally developed. Statements there noting
> that downstream routes, numerical certificates, or `TailObligation` remained
> open at the component level are historical module-scope notes; all full-tail
> obligations are discharged in `Sude/BMORPublishedExplicitFormula.lean`,
> `Sude/FC2KBandTheorem.lean`, `Sude/FWFirstBandTheorem.lean`,
> `Sude/UpperTailTheorem.lean`, and `Sude/AllOddTheorem.lean`.


## Prime-index translation implemented

`Sude.RSIndexLowerSharp` is the separate published hypothesis RS62 Theorem 3,
(3.10): for one-based prime index `j >= 2`,
`j * (ln j + ln (ln j) - 3/2) < p_j`. It is not the weaker (3.12)
`Sude.RSIndexLower` hypothesis. The intended FW application substitutes
`j = n*n+1`; `Sude.fw_poolMaximum_gt_twenty_one_sq` derives `21n² < X`
for `n >= 19485` from that explicit hypothesis. The
published inequality is an explicit hypothesis, not a Lean proof or a global
axiom, and this import inventory remains incomplete.

`Sude.PrimeIndex` proves that `poolMaximum n` is a prime, belongs to the
prescribed pool for positive n, and bounds every pool member. It proves the
exact source lower-index logarithmic envelope S18.11 for n >= 2, including
the source's base-two parameter when `v * ln 2 = ln n`. From RS62 (3.13), it
also proves S18.10's `X < 2^41` for every `3 <= n <= 2^18`, and consequently
every pool entry is less than `10^13`. Those are conditional on their exact
published hypotheses, not on a tail or controller conclusion. The proof uses
mathlib's kernel-checked rational enclosure for ln 2 and exact arithmetic.
Lean also proves the `X < 2^44` part of LZ9 for `3 <= n <= 2^19`; the
remaining LZ9 quantities, all other analytic translations and the controllers
remain open. The machine-readable map also records the selected printed RS62
prime-count statements as pending, without introducing them as Lean hypotheses.


## Bounded progression supply implemented

`Sude.BMORFiniteTheta` is the theta conjunct of the published finite-range
Theorem 1.9, with its complete modulus cutoff and finite computation imported
as stated. `Sude.APInterval` proves the exact `(b,c]` membership and prefix
sum difference, and derives S18.5 by bounding each actual prime weight by
`ln X`. For even reduced classes, `Sude.bmor_even_pool_interval_supply`
connects the resulting count to distinct entries of the prescribed pool for
`3 <= n <= 2^18` and `3 <= q <= 100`. The separate
`Sude.bmor_two_pool_interval_supply` proves the q=2 case via q=4, preserving
the correct larger cutoff. Both require the BMOR theta premise and RS62
upper-index premise as explicit arguments. The companion `Sude.bmor_even_available_pool_supply`
and `Sude.bmor_two_available_pool_supply` subtract the size of an arbitrary
set of previous reservations, and prove the surviving entries belong to the
original pool and are outside that set. The stronger controller-specific
depletion accounting, pair matching and complete controllers remain open.


## Physical switch correspondence

`Sude.Switches` formalizes the equal-gap rectangle trade in RP2 of
`../../problems/prime-line-sums/manuscripts/cutoff2_rectangle_packing.md` and
section 3 of `../../problems/prime-line-sums/manuscripts/explicit_controller.md`.
`rectangleTrade_line_effect` gives all four signed contributions on any
finite labelled line. `rectangleTrade_rows`, `rectangleTrade_columns`,
`rectangleTrade_main`, and `rectangleTrade_anti` specialize that identity to
the public statement's full sums. Both directions of the trade are physical
permutations; support, pool preservation, positive gap, both-diagonal center
membership and center avoidance are proved explicitly.

`Sude.PairSwitch` proves the signed row/column effects of a physical ordinary
pair swap and preservation of the other axis and both avoided diagonals. It
also records the effect on **both** diagonals if the common center is switched.
`Sude.DisjointTrades` proves that disjoint rectangles preserve each other's
actual entries and gap conditions, commute, and can repair opposite diagonals
in sequence while preserving both axes and the exact input pool. Its theorem
`rectangleTrade_main_then_anti` assumes the rectangle cells, gap pairs,
geometry and disjointness are already supplied. It does not by itself establish
the existence of those resources or any controller or flow realization.

`Sude.RectanglePacking.rp1_exact_packing` proves the source RP1 construction
for every `J >= 3` and `2*J+1 <= n`, for arbitrary main/antidiagonal labels.
It proves injectivity and exact cardinality of all `2J` row and column slots,
four distinct cells per rectangle, the designated diagonal and all other
corner exclusions, avoidance of the center, and pairwise disjoint supports.
The proof uses the exact one- and two-step cyclic construction from RP1;
it also holds for even n, though the target theorem concerns odd n.
`packed_main_then_anti` connects the constructed coordinates to RP2 under
explicit equal-gap entry hypotheses.

`Sude.Placement` proves that any finite injective assignment of distinct
pool entries to distinct cells extends to a full exact-pool permutation.
Its reservation-preserving version fixes earlier reserved cells, provided the
new cells and values avoid them. `place_and_trade_packed_pairs` composes this
extension with RP1 and two opposite-diagonal trades, keeping the prior cells
and the center unchanged and preserving all rows and columns relative to the
completed pre-trade placement. It assumes the distinct equal-gap values exist;
it does not give a balanced completion, select the pairs, or discharge a
controller.


## Finite-prefix grid and physical row transfers

`Sude.GeneratedPrefix.actualFirstFourStageFamily` assembles the fully
kernel-checked gap-two, gap-four, gap-eight and gap-sixteen L-stage populations
and proves their endpoint footprints disjoint. Pool membership uses the
explicit `RSIndexLower` premise. The other L stages and controller are not
established.

`Sude.BTStageTrace.physical_seeded_step_grid` proves complete subset sums in
multiples of the base gap for supplied distinct pair labels, provided their
gaps match a traced selection and an additional seed label has the base gap.
`Sude.BTStageTrace.installed_network_step_grid` instantiates the labels with
the physical network slots; `Sude.installed_variable_grid_endpoints` establishes
their common directed endpoints with a seed when that seed has those endpoints.
`Sude.BTStageTrace.extend_installed_network_grid` instead accepts a disjoint
initial physical grid and extends it using the stage slots. Supplying that
initial grid or a distinct physical seed, and deriving the even correction
grid, remain separate obligations.

The above `BTStageTrace` uses a restricted next-gap radius. The separate
`BTGrowingTrace` uses the source recurrence `R + gap`; its iteration,
actual-pool values, installation and initial-grid extension are proved under
explicit numerical and physical hypotheses. The BT6--BT9 shifted-radius,
phase-entry and generic logarithmic growth inequalities are proved without
further imports. No concrete BT phase cap or controller has been discharged.
See `RESEARCH_NOTES.md` for the source-fidelity correction.
The growing trace can also be split at any stage with its exact remaining
stock, and the BT8 inequality applies to that actual stage under an explicit
width hypothesis. A width-preserving iteration and
`BTGrowingTrace.linear_width_reaches_target` compose actual selected stages
with the generic BT9 bound. No concrete stage width or phase data are assumed
proved.
`Sude.mv_growing_linear_phase_reaches_target` composes that selection and
target argument, including early crossing, conditional on explicit published
MV input and numerical premises quantified over all eligible subsets and
radii. It is a phase interface, not an assumed or discharged controller.
The corresponding ordinary AP phase has an elementary short-pair count,
selection and target theorem without an MV premise, under explicit positive
width and uniform numerical conditions. Successive physical traces concatenate
with proved cross-phase endpoint separation. A paid BT7 threshold persists
through later growing stages under a stock floor; paying the numerical phase
thresholds and all controller instantiations remain open.
The generic AP and BT phase interfaces can now derive their uniform
subset/radius numerical data from explicit scalar stock, pair-budget and
phase-entry bounds, and compose these bounds to a target conclusion. This
does not establish the bounds for any selected route.
`Sude.mv_continue_after_paid_entry` composes a prior physical trace with a
BT scalar phase while accounting for a larger actual starting radius and
all cross-phase deletions; its analytic and scalar premises remain explicit.
`Sude.ap_then_bt_from_scalar` composes the elementary and BT phases into one
actual trace under those explicit premises, including a conservative second
stock reserve; `Sude.ap_then_bt_or_finish_from_scalar` also handles finishing
before the BT entry threshold. These do not prove any route's supply or
numerical bounds. The minimum-budget variant charges the ordinary phase only
for the earlier of the BT entry and final targets.
The narrowed variant `Sude.ap_then_bt_narrow_with_minimum_budget` additionally
proves the source's per-stage midpoint-spread invariant. It pays for `zQ`
candidate pairs but deletes only the `Q` retained pairs; it still requires
explicit interval and scalar gate hypotheses and does not discharge a route.
The proved `BTGrowingTrace.placed_network_midpoints` transfers this narrowing
to square entries using the explicit physical placement equations.
The finite screened-pool count and its mod-2, interval and midpoint-span
properties are proved directly for the exact prescribed pool. The size of
the actual reserved set and subsequent scalar gates remain explicit.
`Sude.screened_pool_narrow_prefix` uses these results to specialize the
two-phase selection to the actual `g=2` screened pool. Its sole external
analytic premise is the explicitly parameterized MV theorem; the fields of
`ScreenedPrefixNumerics` are unproved project arithmetic obligations, not
additional trusted imports.
`Sude.BTGrowingTrace.install_screened_narrow` connects the selected screened
pairs to actual row, column and diagonal-rectangle cells, preserving exact
gaps, midpoint bounds, disjointness and prior cells under explicit geometric
and capacity conditions. It does not establish the subsequent line repairs.
FW4's seed quota and the FW allocation-depth bound are proved by
`Sude.fw_seed_quota_gate` and `Sude.fw_allocation_depth_gate` for all four
stated band endpoints. The seed population, remaining FW gates and entire
route conclusion remain open. The source's uniform floor-capacity bound is
proved separately by `Sude.fw_floor_capacity`.
The frozen `A=235, N=16` reflected-band rational geometry and endpoint
coefficients are checked by `Sude.fw_reflected_band_geometry`; actual
prime supplies and endpoint scale bounds remain unproved here.

`Sude.binary_even_grid` proves FPF3's complete grid of even subset sums for
stages with gaps `2,4,...,2^P`, using each stage at most once.
`Sude.completeEvenGrid_insert` proves the bridge rule for a fresh even gap at
most `R+2`, with the exact expanded radius `R+gap`. These are general
arithmetic lemmas; neither computes nor assumes the source's finite tables.

`Sude.verticalPairs_toggle_subset` implements any chosen subset as actual
permutations of an existing exact-pool square, assuming supplied pairs share
the two rows, use distinct columns, avoid both diagonals and prior reserved
cells, and have the stated gaps. It proves the signed effect on all rows,
fixes every column and both diagonals, preserves reservations, and preserves
all unselected pair entries. `Sude.vertical_grid_correction` composes that physical result with any
proved complete grid, including one extended by a bridge.
`Sude.vertical_binary_correction` specializes it to binary gaps. The finite prime-pair populations,
selection and placement into such a physical family, signed controller routing,
bridge realization, and every controller conclusion remain open. In
particular these lemmas do not accept FC2K's 8,742 numerical cases.


## Fixed-gap candidate matching and depletion

`Sude.binary_prime_family_disjoint` proves FPF2's fixed-gap matching from
primality, the lower endpoint bound `p>3`, and a power-of-two gap: three
consecutive terms would include a multiple of three. `pairFootprint_card`
proves that a positive-gap matching has exactly twice as many distinct
endpoints as pairs. `availablePairs_card_lower` proves that each prior
reserved value destroys at most one pair, and `select_available_pairs`
selects any requested number when the original candidate count pays that
charge. `pairEndpoint_injective` and `place_pair_family_preserving` then
install a supplied matching of actual pool values in supplied distinct cells,
while fixing previous reservations. The specific pair populations, primality
certificates, cross-stage selection, pool membership, physical cell geometry
and balanced placement are not discharged by these general lemmas.

`Sude.prime_mem_pool_of_oddPrefix_card_le` proves the FPF1 indexing step:
if the number of odd primes through B is at most n², every odd prime through B
belongs to the prescribed pool. `Sude.select_binary_pool_pairs` composes
that step with fixed-gap matching and reservation accounting, yielding Q
actual-pool pairs and exactly 2Q distinct endpoints when the candidate
population and the prefix count satisfy their explicit inequalities. The five
large numerical prefix counts and candidate counts have not been proved.


## Target-table Lucas certificates

`Sude.Lucas.NodeValid` encodes the FTT certificate's base case and its
recursive factorization, earlier-prime references, modular-power and integer
gcd checks, exponent limits and factor ordering. It does not enforce the
source checker's overall unsigned-64-bit input bound, global node ordering,
exact graph reachability or table schema; those are separate parsing and
coverage obligations. The checker uses binary modular exponentiation with
`powMod_correct`, and `checkCertificate_sound` proves primality of every
accepted node from an empty initial list, using mathlib's proved Lucas
primality theorem. It introduces no external theorem assumption.

`FirstTargetLucas` contains the generated 25-node closure of the three target
primes in the source row for n=2001. Lean kernel reduction accepts this
concrete certificate and proves those three primes. It also checks the row's
integer compatibility, target-radius and mean bounds against the row's
literal X and T. The latter are **not yet proved** to be the prescribed pool
maximum and total. Full node-graph acceptance, complete target-table coverage
and the actual prime-prefix calculations remain open. `scripts/generate_lucas_fixture.py`
recreates this data-only fixture from the pinned FTT JSON.

A direct kernel reduction of the first 1,000 full-chain nodes was stopped after
about 17 seconds and 3 GB resident memory, before producing a result. A
separate exploratory generated proof checked those same 1,000 nodes as
individual lemmas with explicit references to earlier prime lemmas; it
completed successfully. That experiment was not committed as a certificate
or treated as proof of the remaining target table. Scaling requires a
reproducible batched version with checked data correspondence and coverage.


## First hundred target rows

`FTTTargets` defines the FTT row's three prime targets, exact target total,
three integer radius inequalities and strict mean inequalities for the row's
literal X and T. It also checks positivity and oddness of X and targets,
the upper bound on X and the exact integer-domain gates `n*n<X` and
`n*n*X<2^62`. `absDiff_cast` proves that its natural subtraction encoding
is the integer absolute difference. `FTTBounds` proves that each integer
radius inequality gives the corresponding real bound with a positive order.

`FTTFirstHundred` and generated modules N0000--N0004 and R0000--R0003 prove
all 1,052 recursive Lucas nodes needed for the first 100 rows, covering 293
distinct target values. `firstHundred_cover` proves that every odd order
2001 through 2199 has one of these valid rows; this includes the full
interior, not just endpoint evaluations. The recorded X and T are still
literals: the pool-prefix sieve, exact X/T identities and every square or
controller conclusion remain open. The expanded row coverage is stated below.

`python3 scripts/generate_ftt_batches.py` checks the pinned input hash and
regenerates source for the complete 69,609-node graph and all 8,742 rows,
using individual kernel-checked Lucas proofs in topological order. The first 101 node modules and 100 row modules are checked in and
built as part of this checkpoint. Generating the remaining source is not evidence
that it compiles or that any remaining claims have been proved. The optional
full generated aggregator and full-domain coverage have not been verified.
The generator's hash check establishes source identity, not mathematical
truth; the generated proofs must be checked by Lean.

`FTTFirst250` extends the same checked construction to the first 250 odd
orders, 2001 through 2499, proving coverage of that entire interval. Its ten
row modules rely on 2,418 certified Lucas nodes and contain 741 distinct
target values. This is extended by the first-3750 result below; all prime-pool
X/T identities and all controllers remain open.


## Target lists and axis compatibility

`FTTTargetList` constructs the actual list with `n-2` copies of q followed by
P and R, preserving repeated values. For each valid row Lean proves its
length, prime entries and exact total. `targetAt` indexes that list by every
labelled line; all its entries are prime and odd, and satisfy the real
source radius. Lean also proves that every exact-pool placement has the same
pool total, separately for the sums of all rows and all columns.

`pool_target_system` composes these facts with a valid FTT row, conditional
on explicit equalities identifying that row's stored X and T with the actual
pool maximum and total. It includes both axis-total identities and the prime
diagonal target q. These global equalities do not establish individual line
compatibility, the diagonal correction identities, the pool prefix, or any
controller conclusion.

`FTTFirst3750` extends the checked target-table coverage to every odd order
2001 through 9499. Its 150 row modules depend on 30,373 checked Lucas
nodes and contain 11,123 distinct target values. The other 4,992 rows, every
prime-pool X/T identity and all controller conclusions remain open.


## Physical permutation-layer packing

`Sude.LayerPacking` proves the Hall argument in PB section 4 from mathlib's
proved finite Hall theorem. Given a permutation edge layer and at most L
reserved cells per physical row and column, it constructs the bipartite
forbidden sets and proves the source's `2L+4` bound on both sides, including
both endpoints and both diagonals. If `4L+8<n`, a column permutation exists.

For a derangement, `physical_balanced_layer` proves that the resulting 2n
physical cells are distinct, avoid prior reservations and both diagonals,
and contribute exactly two cells to every row and every column.
`place_physical_balanced_layer` installs a supplied injective family of
actual pool entries with the specified pair gaps, preserving all prior
reserved entries. The value supply, its depletion and gap hypotheses remain
explicit; no source prefix population is assumed. `layer_load_update`
charges at most two more occupied cells per row/column, and
`physical_two_layers` composes two such constructions without cell reuse.
The full numeric prime supplies, balancing of the randomized completion,
the remaining integration of the FC2K construction, and all full controller
conclusions remain open.


## Arbitrary finite row and column layer networks

`Sude.LayerPacking.pack_finite_layers` iterates the source's Hall-based
physical matching for any finite list of supplied derangements. Each step
adds its actual cells to the reservation and charges two more cells per row
and column. Lean proves that the resulting supports are pairwise disjoint,
avoid both diagonals and initial reservations, and contribute exactly
`2 * number_of_layers` cells in every row and column. Every layer/edge/side
label maps injectively to its actual cell.

`pack_and_install_finite_layers` places a supplied globally injective family
of actual pool entries across the whole row network, retaining every pair's
specified gap and every initially reserved entry. `pack_and_install_column_layers`
proves the corresponding result in original coordinates via actual square
transposition; both full diagonals, including their common center, are
tracked. `pack_and_install_two_networks` composes the row and column passes:
the second pass protects the entire first support, the two supplied value
families are explicitly disjoint, all pairs retain their actual entries and
gaps, and the combined support contributes exactly twice the total number
of layers to every row and column. `pb9_capacity_for_two_networks` verifies
the PB8--PB9 algebraic load substitution when the number of layers is d*S.

These are conditional physical construction theorems, not prime-supply
certificates or proofs of the expansion graphs. They preserve the specified
reserved cells and installed pairs; arbitrary unreserved cells may be
rearranged during the initial placement. These packing results do not establish balanced
probabilistic completion, all diagonal correction identities,
or any complete tail route.

`Sude.BridgePhysical` connects the selected stage and block indices to the
actual prescribed-pool entries and proves global endpoint injectivity,
including within-block, same-stage and cross-stage cases. Initial reserved
entries are avoided. For `J` stages and `k` double blocks per stage, the
proved total capacity condition is `4Jk + |reservedCells| ≤ n²`, exactly
`2QJ + |reservedCells| ≤ n²` when `Q=2k`; it constructs distinct free
cells rather than assuming their existence. The simultaneous installation
preserves every specified reserved cell and proves both physical equal-gap
equations with the same gaps used by the grid theorem.

`select_grow_install_bridge_stages` composes the previous bridge selection
and grid theorem with this placement. Its numerical per-stage budgets,
initial complete grids, total capacity and BMOR/RS inputs remain explicit.
Total capacity alone does not construct the row, column or diagonal
geometry, nor establish that the initial abstract grids correspond to
installed physical reservoirs. Those connections, the numerical gates and
all complete controller routes remain open.

`Sude.BridgeRectangles` connects a selected subset of the actual bridge
blocks to the previously proved RP1 packing. The four-cell map is injective;
installation preserves earlier reserved cells, yields the exact two equal-gap
equations and leaves endpoints of unselected bridge blocks outside both old
reservations and newly occupied rectangles. A two-rectangle trade theorem
proves the full effects on rows, columns, both diagonals and center while
preserving reserved cells and all other packed rectangles.

`Sude.PackedTradeSequence` extends this to any duplicate-free finite list of
selected packed rectangles. Its exact main and antidiagonal increments are
the sums of the actual selected gaps for the respective labels; all rows,
columns, reserved cells, the center, and unselected rectangles are preserved.
Comparing two physical orientations yields signed differences of those sums.
`install_and_trade_selected_bridge_rectangles` composes placement with these
trade identities. The injective selection of diagonal blocks and rectangle
labels, the disjointness from prior reservations, and the RP1 capacity remain
explicit hypotheses. Ordinary pair geometry, numerical gates, choice of
target correction subsets and all complete controller routes remain open.

`Sude.BridgeRectangleAllocation` constructs injective stage/block and RP1
label maps for exactly `4d` diagonal blocks per bridge stage, with `2d`
assigned to each labelled diagonal. It preserves independently chosen
labels outside the bridge image, proves `4d ≤ k` for FC2K's `d=6` and
`k=6(n+8)/2`, and instantiates the actual-pool rectangle installation.
The total RP1 rectangle bound, disjointness from previously reserved cells,
ordinary-pair placement and all numerical controller gates remain open.

`Sude.BridgeOrdinarySlots` splits the selected `k=Q/2` double blocks into
`4d` diagonal blocks and `rn` ordinary blocks, each ordinary block providing
one pair to each network. It proves global endpoint injectivity, separation
from the diagonal subset and both positive even gap identities. For FC2K,
`d=6`, `r=3` and `k=6(n+8)/2=24+3n`, so the count exactly pays for the
24 diagonal blocks and `6n` ordinary pairs at each bridge stage.

`Sude.BridgeOrdinaryNetworks` reindexes those actual values into row and
column permutation layers, derives the injectivity and reservation-avoidance
conditions, and applies the existing two-network physical matching theorem.
`Sude.PackedRectangleLoads` proves that the whole RP1 packing uses at most
two cells in each row and column, including a joint bound that does not
double-charge previously reserved rectangles. `Sude.BridgeNetworkAfterRectangles`
installs the allocated diagonal bridge rectangles and then both ordinary
networks in the same square, preserving prior cells and the actual diagonal
entries. It also proves that later allocated diagonal trade sequences leave
every ordinary-network entry unchanged, including when comparing two
orientations for signed diagonal corrections. The source PB9 arithmetic is linked
to the bridge layer count, but the numeric gate itself is not certified.

`Sude.BridgePhysicalGrid` relabels a complete grid by an injection on its
finite support, identifies each selected bridge gap with the gap of the
corresponding installed layer/edge pair, and proves the grid statement for
the packed physical pair structure. A canonical list repeats a chosen family
of permutations at every stage; its derangement and common-endpoint properties
are proved. These lemmas introduce no analytic imports. They assume the
selected stages, initial grid, placement and stopping inequalities supplied
by their callers; they do not establish the actual graph's expansion and
controller gates.

`Sude.NetworkPairJoin` preserves initial physical pairs when their reserved
cells are unchanged and joins them to disjoint packed layers. In
`Sude.BridgeJoinedGrid`, the resulting old and new pairs form disjoint,
complete per-edge grids with common endpoints and a `CenteredNetwork` on
the physical placement. It still assumes the existence and reservation of
the initial pair system, the required initial grids, repeated graph layers,
selected bridge stages and numerical stopping hypotheses. It does not prove
the graph expansion, pair supplies, or a complete controller.

`Sude.PrefixPhysicalGrid` connects FPF3's gaps `2,4,...,2^P` to an
injectively labelled physical pair system, proving the exact radius,
evenness, disjoint edge blocks and endpoint interface required by the joined
network. The physical pairs and their prescribed gaps remain hypotheses;
this is not a certificate of the five FPF populations or an unconditional placement.

`Sude.PrefixPairAllocation` partitions each supplied stage into distinct
diagonal and ordinary pair indices and proves the exact FC2K count
`48 + 6n = 6(n+8)`. It installs all diagonal pairs in RP1 rectangles and
the remaining row and column pairs in disjoint packed layers in the same
square, retaining reserved cells and the actual power-of-two gap equations.
`Sude.PrefixInstalledNetwork` proves that repeated permutation layers
give the installed pairs the complete centered per-edge grids. The supplied
pool population, its cross-stage endpoint injectivity, gap identities,
free rectangle cells, graph derangements, and numerical capacity remain
explicit hypotheses; this proves neither finite FPF certificate acceptance
nor a complete controller. No analytic imports are added.

`Sude.PrefixPopulationCoverage` proves the diagonal and ordinary endpoint
allocation is bijective under the exact stage count. After installation,
the image of the actual rectangle and network cells is exactly the image
of the full retained pair population. Its endpoint injectivity gives the
source's full `2QP` deletion budget. These are conditional consequences
of the supplied physical population and placement, not finite certificate
acceptance or an estimate of later interval intersections.

`Sude.PrefixTruncation` proves source-order truncation, gap preservation,
injectivity, the exact retained endpoint count, and freedom of all unused
suffix endpoints, conditional on a supplied globally injective full profile.
It imports no further analytic premise or finite certificate acceptance.

`Sude.FinitePrefixPoolBound` derives three FPF endpoint containment results
from the existing `RSIndexLower` import: `X>60,000,000` for `n≥2000`,
`X>74,000,000` for `n≥2400`, and `X>1,800,000,000` for `n≥10000`.
The C27 cutoff is its endpoint interval's upper limit, not its 95-million
sieve bound. This replaces the need for the corresponding three odd-prime
prefix counts when proving membership of the actual source endpoints. The
L-stage sample in
`Sude.GeneratedPrefix.FirstFamilyPairs` checks 96 endpoint primes, their
distinctness and source binary gaps with 305 Lucas nodes. It proves pool
membership for these samples under `RSIndexLower`; it does not prove the
other L pairs, source stream selection, or full certificate acceptance.

`Sude.FiniteDistinct` proves that acceptance of its structurally recursive
bit-trie checker implies finite injectivity. Limited depth can cause false
rejection, never a false acceptance. `Sude.GeneratedPrefix.L8` uses it for
192 source pairs and checks 1,652 stage-local Lucas nodes to establish all
384 endpoint primes and their original power-of-two gaps. The stage-split
generator reproduces the pinned full L stream and takes its first eight
pairs per stage; hashing establishes provenance only.
`Sude.FiniteDistinctChunks` proves the sound composition of exact trie
state transitions and `Sude.GeneratedPrefix.L32Distinct` kernel-checks
24 successive source-slice checkpoints, proving 1,536 endpoints distinct.
`Sude.GeneratedPrefix.L32Primes` separately checks primality for all of
them with 5,037 stage-local Lucas nodes and proves the exact gap and pool
interfaces. The states are defined from earlier insertions and full-scale
complexity remains open. None of these results accepts the complete finite
population.

`Sude.TrieChunkAppend` proves concatenation of separately verified trie
checkpoint sequences and derives injectivity for the union of their finite
enumerations. `Sude.PrefixL64` applies this to source pairs 1–32 and 33–64
at every L stage, with 5,154 further stage-local Lucas nodes for the second
block. It proves primality, cross-block distinctness, pool membership and
exact power-of-two gaps for the resulting 3,072 endpoints. This is still a
finite slice; it neither accepts the complete FPF population nor proves
the lower controller.

`Sude.PrefixStageCertificate` turns checked Lucas nodes, sorted endpoint
data and exact range bounds into mathematical prime-pair blocks. Strictly
separated accepted blocks compose, and the existing binary-gap matching
theorem supplies actual pool membership and the exact endpoint count.
The checked `LStage0.All` contains all 452 blocks and 14,448 pairs in the
first L stage. Under `RSIndexLower` and `n ≥ 2000`, Lean proves the endpoints
are 28,896 distinct entries of the prescribed pool, with gap two. Source hash
reproduction supports provenance; the block and aggregate proofs establish
the stated facts. The remaining 23 stages and cross-stage disjointness remain
open, as do the other profile populations and the controller.

`Sude.PrefixStageIndex` and `Sude.PrefixStageFamily` derive the allocator's
indexed, injective pool-value interface from stage certificates, with
cross-stage endpoint separation explicit. The family constructor does not
claim that the required separation has been checked. For `2001 ≤ n ≤ 2400`,
`Sude.GeneratedPrefix.LStage0.install_certified_stage` instantiates the first
stage using `RSIndexLower`, checks the physical packing inequalities, and
identifies both the exact entry at every allocated cell and the full used
population of `2 * 6 * (n + 8)` entries. This does not prove the remaining
stages, completion, adequate routing radius, or any tail route. The source
list is named irreducibly to avoid expanding 14,448 entries during Lean
elaboration; the equality to the accepted list is retained in its definition.

All 14,448 source pairs of L stage one have been accepted in 452 blocks,
including 93,899 local Lucas nodes. The full aggregate compiled before
promotion, and regenerating the source blocks reproduced their hashes.
`firstStage_disjoint_secondStageCheckpoint` proves their entire footprint
disjoint from the 14,448 accepted stage-zero pairs using certified endpoint
ranges. `actualFirstTwoStageFamily` and its value interface assemble both
actual accepted stages and prove global injectivity and source gaps, using
the existing RS lower-index premise for pool membership. The other 22 stages
and their global separation remain unproved.
`fullPrefix_realizes_demands` assumes a complete globally separated 24-stage
family and proves the L-band packing and actual integral routing interface
with explicit radius and demand inequalities. It preserves both diagonals,
the rectangle reservation, and the prescribed pool. The full family and
the numerical target/completion hypotheses remain open; the theorem is not
a tail-route conclusion or an additional external import.

The central completion source CC2 is partially formalized by
`central_unused_entries_select`, `central_stock_after_deletion`, and
`central_entries_actual_mean_update`. These prove one exact-size selection
from distinct labelled unused values, charge deletions against each outer
stock, and derive the signed mean change. They add no analytic import.
`central_source_diagonal_batches` then proves all three successive selections
and persistence of their prerequisites from CC1--CC2's explicit stock-size,
mean and two-sided stock hypotheses. `central_source_batches_with_total_error`
also derives CC10's `3η` bound for the combined deviation from the original
mean, by the exact signed mean-change identity. The composed
`central_source_batches_with_diagonal_errors` proves both CC11 diagonal bounds
using the source's denominator and cardinality hypotheses.
`central_place_odd_diagonals` places the selected values into the actual free
diagonal cells, proves the unique odd-square center and preserves all prior
reserved cells, with CC11 bounds on the full labelled diagonal sums. It
requires an unreserved center and explicit supplied-stock, mean and outer
count hypotheses. `central_place_odd_diagonals_exact_pool` identifies that
stock with the exact prescribed entries outside the old reservation, derives
its count from the reserved-cell count, and proves the exact remaining-pool
identity, combined `3η` deviation, and exact remaining-mean update after the
diagonal placement. The actual stock-count lower bounds,
mean estimate and the remaining parts of off-diagonal completion remain open.

The matching-decomposition portion of RF1 is proved in
`Sude.RegularFactorMatching`, using mathlib's proved finite Hall theorem and
finite double counting. For any supplied `k`-regular physical cell set, Lean
constructs `k` pairwise-disjoint perfect matchings, proves their exact union,
and gives a bijection between matching/row labels and factor cells.
`Sude.sorted_regular_factor_completion` then assigns the exact unused pool in
sorted matching blocks, preserves all reserved cells and both diagonals, and
bounds each row and column error by the supplied strict width of that pool,
relative to fixed entries and its actual mean. It assumes the entire
unreserved support is a positive regular factor. The central-stock supply
and source-specific mean and capacity estimates remain separate obligations. No additional analytic input
is used for this conditional construction. `dense_factor_source_cuts` proves
the full family of RF1 physical cut inequalities, including the source
ceiling and the transpose case, from explicit degree and non-underflow
hypotheses. `directed_unit_flow_of_cut_inequalities` proves an integral zero-or-one flow
from all directed cut inequalities by residual paths and finite termination.
`dense_residual_regular_factor` translates the physical cuts into those
directed inequalities and extracts a regular factor from the resulting
zero-or-one physical flow. `dense_central_stock_completion` composes it with
RF2 under explicit degree, positivity, central-stock and width hypotheses;
no additional external import is used. `balanced_residual_central_completion`
derives the exact RF3 residual and factor parameters from the reserved-cell
occupancy bounds, and proves the prescribed pool's strict width using its
actual maximum. `bmor_central_stock_full_reservation` derives a bounded central-stock count
from the existing BMOR theta and RS upper-index hypotheses while charging the
entire reservation. `bmor_balanced_residual_completion` composes this with the
physical completion under explicit interval and numerical gates. This is a
conservative alternative to the source's allocation-specific deletion budget;
its gate has not been verified for a controller. The source's outer-band
separation and the RF10 central-stock count are now proved with an explicit
bound on the reserved entries in the central interval. The charged bound is
composed with physical completion in `bmor_balanced_charged_completion`.
`actual_unused_mean_from_reserved_pairs_source` proves the original-mean
comparison from globally distinct physical reserved pairs and explicit
midpoint budgets, including the exact `T/n²` normalization and remaining
count. The actual controller pair classification, reservation cover and
deletion budget, numerical gates, occupancy and prime targets remain open.
`central_diagonals_from_reserved_pairs` composes the mean estimate with
physical central-diagonal placement, and `central_diagonal_rows_columns_transfer`
proves the exact effect of that preassignment on every row and column.
The latter includes both diagonal cells, their possible shared center, and
the actual remaining-pool mean shift. `packed_layers_post_diagonal_occupancy`
then derives RF3's physical occupancy interval from the proved packed-layer
balance and explicit exceptional-support budgets. These introduce no external
premise. `bounded_central_construction_from_pairs` composes the pair-based
mean comparison, actual diagonal preassignment, RF10 charged stock, regular
factor and physical completion. Its explicit `PostDiagonalAnalyticInputs`
requires interval, depletion and numerical gates uniformly for admissible
diagonal placements. Controller pair/stock supplies, those gates and prime
corrections remain open. `post_diagonal_inputs_from_pair_budget` derives that
uniform interface from explicit pair budgets, scalar margins and the actual
reserved-value classification, using a floor-safe mean-shift bound. The
controller must still prove those inputs. `bmor_two_diagonal_window_supplies`
separately derives the two actual diagonal-selection stocks from the same
published inputs, with explicit interval, deletion and numerical gates. No
controller has yet discharged these conditions; this is not a complete tail
route.

`Sude.PrefixThetaCount` proves actual upper prime counts at 150 million and
450 million from the already declared `RSIndexLower` and `BMORFiniteTheta`
inputs. The proof splits half-open intervals exactly, uses BMOR with q=1,
and bounds logarithms and square roots by rational inequalities. Its M and H
pool bounds, together with the previous L, C27 and T bounds, give
`Sude.fpf_profile_prime_in_pool` for all five actual FPF endpoint ranges.
This is a replacement for the source's finite count route to pool membership,
not a proof of the source's exact odd-prime counts, the target-table pool
identities, or existence of the retained pair populations.

These results still require the actual derangements, their expansion,
explicit numerical capacities, side-stock gates, suitable prior reservation
invariants and initial-grid interfaces. They do not establish the balanced
random completion, diagonal target selection or any complete tail route.


## Physical network switching and centered grids

`rowNetwork_toggle_subset` performs any selected finite family of actual
disjoint vertical pair swaps and proves the exact signed row transfer, fixed
columns, both fixed diagonals and equality of every untouched cell. The
corresponding column theorem uses the proved square transposition. Packed
row and column layers are converted to those pair systems from their actual
installed gaps; `toggle_two_installed_networks` performs both passes while
keeping the second network's entries intact during the first pass. It proves
all row and column effects, both diagonal identities, initial reservation
preservation, and the exact pool permutation.

`repair_two_networks_of_selected_transfers` proves the target axes if the
actual selected subsets have the specified transfer sums.
`square_of_selected_network_transfers` consequently reaches the public square
only under explicit inputs: an installed placement with prime diagonals,
prime row and column targets, and actual subsets realizing all demands.
Those inputs are not imports or established controller conclusions.
`selectedTransfers_sum_zero` and `selectedTransfers_even` prove necessary
conservation and parity, but do not prove existence of a flow or subsets.

`centered_even_grid` proves the two-sided even correction interval around a
fixed lower midpoint, with exact midpoint rounding and binary-prefix total.
`vertical_centered_reference` chooses one physical reference orientation
before the demanded correction and realizes every even signed correction
within its stated radius, while retaining columns, both diagonals and the
caller-specified reservations. This is one reservoir; adequate pair
populations, completion, and all tail routes remain open.


## Simultaneous centered reservoirs and supplied integral flows

`simultaneous_centered_subsets` chooses a single reference subset for each
of a finite family of pairwise-disjoint reservoirs, then constructs all
subsets simultaneously for any supplied signed even transfers within their
individual centered-grid bounds. `twoNetworks_centered_transfers` connects
those choices to actual installed row and column pairs, preserving the fixed
reference, both diagonal sums, the initial reservations and exact pool while
proving every directed vertex effect. Each complete grid, the pairwise
disjointness and the common endpoints are explicit, unproved caller inputs.

`twoNetworks_realize_bounded_integer_flows` specializes this construction
to actual integral edge values bounded by `floor(N/2)`, provided each
reservoir's proved even grid extends through at least `2N`. It realizes
twice the signed divergence in the physical square. The center is computed
from the stated grid radius; identifying it with the actual pair-midpoint
reference additionally requires proving that radius equals the sum of the
actual gaps. `fc2k_floor_capacity_gate` verifies the exact integer rounding
step used with `N=KX>=2000` and the printed `999/1000`, `199/200` factors.

`twoNetworks_square_from_integral_flows` then proves `HasSquare n` when
explicit bounded integral flows have exactly the target divergences, the
line targets are prime, and the starting placement has prime diagonals.
The reference is chosen before those targets and flows, and it preserves the
starting diagonal sums and reserved entries.

These supplied-flow results do not establish the FC2K expansion hypothesis,
the finite prime reservoirs, or prime reference diagonals. In particular the complete
tail and all eleven routes remain open.


## FC2K cut inequalities

`Sude.CutRouting` formalizes FC2K section 7, equations (FC2K14) and
the subsequent demand-box/capacity comparison. `zero_total_cut_demand`
bounds a zero-total integer demand on either side of every cut;
`scaled_cut_capacity` proves the exact integer scaling argument; and
`fc2k_cut_inequalities` combines these with `fc2k_floor_capacity_gate`.
The statement assumes a finite edge-index type, so parallel edges count
separately, and explicitly assumes the source's 199/200 expansion bound,
`N >= 2000`, the stated strict demand bound, zero total and the demand box.
No expansion graph is constructed by these results.

`edgeTransfer_cut_bound`, `bounded_flow_cut_inequality`, and
`bounded_flow_necessary_conditions` also prove that the physical
`edgeTransfer` sign convention obeys the corresponding cut conditions and
zero-total identity, including loops. These cut results establish necessity; the sufficiency theorem and physical
connection are proved separately below. All complete tail routes remain
open. No new import was introduced.


## Residual routing and termination

`Sude.ResidualRouting` formalizes the residual-path part of the integral
max-flow argument referenced in FC2K section 7. A residual-closed cut is
proved saturated in the outward direction, so the cut inequality forces its
residual demand sum to be nonpositive. The set reachable from all positive
residual vertices is closed; hence `residual_positive_reaches_negative`
constructs a path to a negative residual vertex. Parallel edges and loops
are included, and both edge orientations are explicit.

`residual_arc_unit_adjustment` realizes a single arc as a unit change of an
actual indexed edge. `apply_unit_adjustment` proves capacity and divergence
for a supplied simultaneous adjustment; `unit_transfer_decreases_mass`
proves the exact decrease of two in the integer absolute residual sum; and
`routing_by_unit_augmentations` proves termination. Finally,
`routing_of_residual_path_adjustments` composes cut feasibility and this
termination argument, conditional on converting an arbitrary residual
path into simultaneous capacity-preserving unit edge adjustments. That
construction is now proved in `Sude.SimpleResidualPath`, as described below.


## Integral routing and physical realization

`simpleDirectedPath_of_reachable` removes directed loops while preserving
endpoints. `simple_residual_path_adjustment` proves that a simple path's
selected indexed edges are distinct and constructs one simultaneous signed
unit change per edge. `integer_flow_of_cut_inequalities` composes this with
the prior residual and termination results to prove the finite integral
cut theorem for zero-total integer demands and uniform capacities, including
parallel edges and loops. It has no flow-existence or path-construction
assumption. `fc2k_integral_flow` discharges its cut premises from FC2K's
explicit demand box, expansion and rounding gate.

`twoNetworks_realize_cut_demands` takes installed disjoint physical row and
column reservoir systems and constructs a single reference before the
zero-total demands are selected. For every pair of demands satisfying the
cut inequalities, it proves existence of an actual pool permutation with
exact row and column effects, preserved labelled diagonals and reservations,
and injective use of the prescribed pool. `twoNetworks_realize_fc2k_demands`
proves the same conclusion from the explicit FC2K demand box and expansion
hypotheses. These are not full controllers: prime-pair supply, actual
reservoir grids, balanced completion, suitable
prime targets, diagonal repairs and all tail routes remain open. No new
analytic import was introduced.

## Actual midpoint and finite-target composition

`EvenGapChain` records every appended physical gap and the coverage
available immediately before it. `extend_even_gap_chain_actual_total`
proves a complete even grid through the actual sum of its distinct gaps;
`binary_prefix_actual_grid` establishes the binary-prefix base case.
`oriented_pairs_midpoint_identity` proves the exact identity between actual
low/high pair entries, the selected reversed gaps and the full gap sum.
`complete_grid_has_true_midpoint_reference` supplies a reference within one
unit of the true aggregate midpoint, with the doubled integer error explicit.
The actual selected prime pairs and the chain inequalities remain inputs.

`halfLineDemand_system` proves conservation of the integer half-demands
when odd line targets have the same total as the current odd lines.
`fc2k_square_of_ftt_targets` composes the FTT target list and both physical
networks to obtain `HasSquare`, assuming an exact pool-total identification,
installed reservoirs, expansion, numerical gates, prime diagonals and
per-line baseline bounds. It does not prove these controller inputs or any
complete tail route, and introduces no new analytic import.

## Finite prefix specification and segment checker

`pool_eq_prefix` and `poolTotal_eq_prefix_sum` identify the prescribed pool
and its sum with the complete odd-prime prefix through `poolMaximum`.
`pool_identities_of_oddPrefix_certificate` proves that a prime endpoint,
an exact odd-prime count and an exact odd-prime sum establish the FTT X/T
identities. These statements include the empty pool at order zero.

`passesPrimeBase_iff_prime` proves exact bounded trial division from a
complete finite base of primes, when the candidate is below `(bound+1)^2`.
`checkedOddSegment_spec` identifies its half-open odd segment with the
mathematical prime segment; `checkedOddSegment_additive` proves adjacent
segment counts and sums compose without gaps or overlaps. The checker is a
simple trial-division implementation, not the source's segmented sieve,
and its performance at tail scale has not been established. The composition
`checked_prefix_pool_identities` requires proof of checker acceptance;
it does not assume the source program or its output is correct.

`Sude.SieveProgression` proves that the first marked value is the source's
`max(p², ceil(lo/p)*p)`, adjusted by p if even, and that all subsequent odd
multiples are precisely its `2p` progression. It translates this into the
finite odd-index progression with stride p, proving the exact count of marks
and correctly handling empty segments and boundary equality. `Sude.MarkedSieve`
unions these progressions for the odd base primes and proves the unmarked
values equal the mathematical odd-prime segment. `Sude.MarkedPrefix` proves
that accepted counts and sums of this finite-set marking construction give
the prescribed pool identities. The definitions do not formalize the C++
implementation, use a bit-packed array, or establish large-prefix acceptance
or full-scale performance.

The first target row's recorded endpoint 67,939,607 has a Lean-checked Lucas
certificate, `first_ftt_max_prime`. Its prime index and recorded total are
not established: `first_ftt_pool_identities_of_verified_prefix` displays
the still-required count and sum. No FTT tail prefix count or sum has been
accepted by Lean, and no complete tail route follows. No new import was added.

`Sude.FactorSegmentCertificate` adds a different, explicitly checkable
certificate: each consecutive odd candidate has either a proper divisor or
is present in a checked Lucas graph. `factor_certificate_segment` proves
that the accepted survivor list is exactly the mathematical odd-prime
segment; `factor_certificate_count_sum` proves its count and sum without
assuming the generated results. `scripts/generate_first_tail_segment.py`
reads the hash-pinned FTT input and emits untrusted certificate data. Lean
has checked its 33 Lucas nodes and 54 candidate rows and proved that the
half-open interval `[67939501, 67939609)` contains seven odd primes summing
to 475,576,967. This is one segment near the 2001 endpoint, not the entire
prefix; no full tail prefix count, sum, or performance claim follows.

`Sude.SegmentedScan` counts and sums the actual unmarked indices and proves
that arbitrary adjacent segment widths, including zero widths, reconstruct
the exact prime interval. `markingSegmentScan_append` combines separately
verified scans without re-evaluation, and `uniformScan_pool_identities`
connects an accepted fixed-width scan to the prescribed pool. The fixed-width
plan handles its final remainder exactly; acceptance is still required.

Kernel reduction has accepted 32 width-16 segments over `[3, 1027)` with
171 odd primes and sum 80,187, and another 32 over `[7171, 8195)` with 112
odd primes and sum 859,924. The intervening region has not been checked by
the finite-set scan; it is checked by the bitset scan below. A one-shot
4,096-candidate finite-set trial, using `decide +kernel`, was
stopped after about 29 seconds when sampled resident memory was roughly
3.8 GB on the shared machine; it produced no theorem. This failed approach
is evidence against assuming the current finite-set scan scales to the full
first-tail prefix. No external or native evaluation is treated as proof.

`Sude.BitsetSieve` encodes the same progression indices in `Nat` bitsets,
proves each bit agrees with the finite-set marking predicate, and proves its
segment summaries and scans equal the previous exact construction. An initial
version converted a finite set to a list; kernel evaluation got stuck at the
choice-based conversion. The executable input was changed to an explicit
prime list, with completeness proved separately. This repair introduces no
trust extension.

The bitset version subsequently passed `decide +kernel` on two separate
blocks of 4,096 consecutive odd candidates, each in 64 width-64 segments.
Lean proves that `[3, 16387)` has 1,899 odd primes with sum 14,584,639.
For the first block, a direct kernel run took 60.69 seconds on the shared
machine; sampled process memory reached at least about 2.58 GB, which is not
a measured peak. The second direct run took 158.31 seconds under shared load.
This fills the earlier gap between the two 512-candidate blocks but does not
establish feasibility or acceptance for the approximately 34 million odd
candidates before the 2001 endpoint.

`Sude.StreamingBitset` proves that a single recursive traversal of each
marked bitset gives the same count and sum as the preceding finite-set
extraction and hence the same pool interface. Kernel evaluation of sixteen
width-1024 segments establishes that `[3, 32771)` contains 3,511 odd primes
with sum 54,056,761. On this shared machine a direct 16,384-candidate
streaming check took 51.15 seconds; the corresponding nonstreaming bitset
test took 27.17 seconds under different load, so these timings do not prove
a speedup. A one-shot 65,536-candidate streaming test was stopped after
about 31 seconds at approximately 3.8 GB sampled resident memory and proves
nothing. The remaining prefix and all controller conclusions remain open.

`Sude.PrunedBitset` proves that removing list entries with `p²` at least the
segment's exclusive upper bound preserves every marked bit and the whole
streaming scan, including duplicate entries and the square-at-boundary case.
The proof uses the already established progression specification and adds no
assumption. Two separately kernel-accepted 8,192-candidate blocks extend the
proved initial count to `[3, 65539)`: 6,542 odd primes with sum 202,353,622.
The resulting count still covers only a small fraction of the 2001 prefix.

An exploratory single 16,384-candidate pruned check of the added interval
succeeded in 27.33 seconds with a reported peak resident size of 4,292,984,832
bytes on the shared machine. To limit resource use, the retained source splits
that check into two modules. These observations do not establish a speedup or
feasibility for the full prefix, and no controller or tail route follows.

FC2K5's repeated-difference step is formalized in `Sude.DoublePairStock`:
more cross-pairs than possible differences give two pairs with the same
positive difference and four distinct entries. `even_span_card_le` proves
that even integers in an integer interval of length `2H` occupy at most
`H+1` values, including an odd lower endpoint. The deletion lemma pays for
each side separately. `Sude.DoublePairBatch` proves by sequential removal
that initial stocks of at least `M+2k` per side and `M²>H+1` give `k`
mutually disjoint double blocks; the actual-pool specialization also pays
for earlier deletions and derives evenness of every gap. `Sude.DoublePairPlacement`
installs a selected list simultaneously into supplied injective physical
cells, preserves earlier reserved cells, and derives each pair of positive
rectangle-gap equations.

`even_real_span_int_bounds` and `even_real_span_card_le` now translate an
arbitrary real interval of length `2H` to the `floor(H)+1` even-gap count;
`real_square_gate_implies_floor_gate` derives the integer gate from FC2K5's
real inequality. `select_pool_double_pairs_fc2k` composes these facts with
the batch selection. Deriving its gap-window hypothesis from FC2K's concrete
endpoints remains open. No lower bound on the actual side stocks, stage
count, placement geometry or diagonal target has been discharged here, and
no complete controller follows. The separate blocks may have different
gaps, as FC2K requires; no independence of choices is assumed.

`Sude.FC2KBridge` formalizes the checker-style half-open bridge windows with
`min(R,X/2) = min(R/X,1/2) X`, width `3 min(R,X/2)/100`, strict cross-gap
bounds, evenness for actual pool primes, and the exact `47/50` growth
increment. It derives the common Wb stock lower bound for both windows from
the explicit `BMORFiniteTheta` and `RSIndexUpper` hypotheses for the stated
finite order domain. The selection theorem charges the intersections of the
existing reserved set with each actual window; it still requires the real
stock-budget and square-gate inequalities. A fresh admissible gap extends a
complete even grid even if its integer radius exceeds the source's real
lower bound.

`Sude.BridgeIteration` proves the source recurrence stops after finitely many
stages and proves all-stage grid preservation under supplied fresh even gaps
with the required stage-dependent bounds. Its completion theorem is
conditional on those gaps being supplied at every preterminal stage. It does
not prove the per-stage numerical budgets, simultaneous physical placement,
or any complete controller route.

`Sude.BridgeDepletion` proves that earlier batches can reduce a current
side stock only through initially reserved entries in that stock or through
earlier same-side windows that meet it. Each batch contributes at most `2k`
entries per side; opposite-side windows from different stages are disjoint.
`Sude.BridgeStageSequence` uses those bounds to select each finite stage
against its actual accumulated reservation and proves disjointness across
all stages. `Sude.BridgeWindowOverlap` proves that geometric half-open
window overlaps conservatively count actual prime-stock overlaps and uses
the corresponding source budget to select the complete recurrence.
`Sude.BridgeChosenGrid` reads the gaps from the selected blocks, extends
each indexed initial grid using fresh sum-type labels, and composes these
facts in `select_bridge_and_grow_grids`.

This composition still has explicit BMOR and Rosser--Schoenfeld hypotheses,
the numerical geometric budgets and square gates for every preterminal
stage, and actual initial complete-grid hypotheses. It does not establish
the numerical certificates, the physical cell assignment, diagonal repairs,
or any complete tail route.

`Sude.FC2KExpansionGate` proves FC2K1 for all real `n ≥ 2001`, the
conditioned small-cut inequality, and both entropy endpoint inequalities.
It uses mathlib's `Real.log_two_lt_d9`, `Real.log_two_gt_d9` and
`Real.log_three_lt_d9` and adds no analytic import. The endpoint-maximum
argument is discharged by `Sude.fc2k_entropy_convex` for the actual controller
parameters, so `Sude.fc2k_entropy_interval_gate` covers the whole source
interval. `Sude.PermutationExceptions` completes graph existence below.

`Sude.PermutationConditioning` derives the one-third derangement bound from
mathlib's exact recurrence, and proves the finite-union conditioning step
for triples without a new assumption. Subsequent modules prove the cut-event
bounds and connect them to expansion.

`Sude.PermutationCuts` proves the permutation cut-count identity, cut
complement symmetry and the exact FC2K expansion interface conditional on
the two explicit failure-set cardinality bounds. It adds no import premise;
the subsequent modules prove the probability/counting estimates needed to
discharge the condition.

`Sude.PermutationSampling` proves the exact finite uniform-image and
hypergeometric counting laws from permutation bijections and finite set
cardinality, with no probabilistic or analytic import. Subsequent modules
prove the three-permutation tail and union bounds.

`Sude.PermutationJointLaw` derives the exact joint sampling and fixed-cut
failure-count identities from the proved finite laws. It adds no new
external import; subsequent modules prove the entropy and union bounds.

`Sude.PermutationCutUnion` proves equal fixed-cut counts for equal sizes,
groups the union bound by `choose n s`, and derives the FC2K expander from an
explicit finite-sum budget. It adds no import. The following modules prove
the sufficient numerical bounds.

`Sude.BinomialEntropy` proves binomial coefficient and lower-tail entropy
bounds, including the FC2K rational-threshold specialization, from the
finite binomial expansion. It introduces no analytic import. The rest of the
small-cut probability is completed by the modules below. `Sude.BinomialMode`
proves the large-cut G2 lower binomial estimate, including endpoints, without
an import; the large-cut estimate follows in `Sude.PermutationEntropyMax`.

`Sude.PermutationEntropyMax` proves the large-cut entropy maximization and
the whole large-cut conditioning budget for every `n ≥ 2001`, using library
concavity and previously proved finite and numerical estimates. It adds no
external premise. The small-cut budget and graph existence are now proved by
`Sude.PermutationExceptions`, as described below.

`Sude.PermutationContainment` proves exact finite containment counts and
the source power bound, for one or any finite family of independent
permutations. No analytic import is added; the exception-pattern union and
small-cut budget are discharged in `Sude.PermutationExceptions`.

`Sude.fc2k_permutation_expander_exists` proves the source's three
derangements and `199/200` routing expansion for every `n ≥ 2001`, using the
proved finite sampling, exception union, entropy and conditioning bounds.
It adds no external premise. Controller supply, placement, completion and
numerical gates remain open.

`Sude.fc2k_install_expanding_prefix` uses that existence theorem and the
proved prefix allocator to install the same labelled expanding graph on two
disjoint physical pair networks, while preserving the rectangle placements
and reserved cells and identifying the supplied entry at every pair cell.
`Sude.fc2k_route_installed_prefix` uses the installed
centered networks and the integral-flow theorem to realize every admissible
pair of bounded zero-total demands, preserving both diagonals and the exact
pool. The prefix population, packing and radius conditions remain explicit;
no external premise or controller conclusion is added.

`place_central_exceptions_and_complete_factor` selects enough values from the
actual central stock, places them in the physical cells outside a supplied
factor, proves the exact remaining-pool identity, and completes the factor.
`central_stock_regular_factor_completion` composes the physical row/column
accounting and mean-shift bound and derives the total deletion budget from
per-row exceptional degrees. The result is the RF2 line error
`X + 2t·radius` relative to the original pool mean, under an actual positive
regular factor, central-stock supply and exceptional-degree bounds. The source-specific stock and capacity supplies remain unproved.

## FW seed and bridge separation

`FWSeedBridge` proves the physical endpoint separation and quota-selection
step of FW2, conditional on the finite seed matching, its pool membership,
the source bridge window and `4 * 2^30 < X`. `FWPoolBound` derives the maximum bound from the explicit RS prime-index
premise; `FWActualSeed` also derives pool membership and disjointness from
the seed-primality facts. The finite seed population and controller remain
unproved internal obligations.

## FW narrowest seed groups

`NarrowSeedBounds`, `NarrowSeedSorted`, `NarrowSeedPhysical`, and
`NarrowSeedRetained` prove the NS1–NS4 width arithmetic, finite choice of
narrowest groups including ties, ordered-range bound, actual endpoint
injectivity and exact reservation accounting. `NarrowSeedMidpoints` proves
that the width is the actual midpoint span. `FWNarrowReservation` applies
these to FW's candidate quota and explicit RS index premise. Its finite seed
population and bridge window are unproved construction hypotheses; no
probabilistic allocation or controller is imported.

## FW narrow seed physical placement

`NarrowSeedExtra`, `NarrowSeedPoolValues`, `NarrowSeedPlacement`,
`NarrowSeedStageMidpoints`, and `NarrowSeedPlacedMidpoints` prove the
physical reindexing, placement and midpoint transfer for retained pairs.
`FWNarrowPlacement` specializes this chain to FW's sixteen groups and
degree-six seed layout, with all selection and physical hypotheses visible.
The population, bridge realization, required derangements and capacities,
probability allocation and controller remain open obligations.

## FT finite twin-prime sieve

`TwinSegmentSieve`, `TwinSegmentScan`, `TwinStreaming`, and
`PrunedTwinStreaming` prove exact local and compositional scan semantics.
`FiniteTwinSeed` identifies the full matching and its 512-segment plan;
`FiniteTwinFlexible` permits independently proved subsegments. Its
lookahead assigns a boundary pair to the preceding lower-endpoint segment;
the packet checker assigns it to the following prime segment, so per-segment
counts are not interchangeable. A kernel-checked prefix proves 500 pairs;
the acceptance of the full 3,650,551 count remains an explicit, unproved
internal computation. `FWFiniteTwinIntegration` shows its intended use
without importing that count as an external theorem.

`ActiveTwinBase` proves that entries with no mark in a segment can be
removed without changing the bitset or streamed count. `FiniteTwinActive`
uses this proved optimization with the same explicit FT acceptance obligation.

`FiniteTwinNewNodes` supplies 645 newly kernel-checked Lucas nodes for
the FT prime base, reusing previously checked FTT nodes. `FiniteTwinOddBaseComplete`
proves the explicit list is a complete base through 32,768, using 55 checked
blocks, its checked strict ordering, and the previously proved prime-prefix
count. The full FT pair population remains unproved.

`FiniteTwinBounds` combines disjoint checked low and high blocks to prove
a 2,764-pair lower bound in the FT set. It does not establish the full count.

`generate_twin_segment.py` reads a hash-pinned FT table to generate untrusted
count hints and Lean certificate modules. Only the first two modules have
been accepted in the current checkpoint; generation and table comparison are
not proofs of the remaining counts.

`generate_twin_aggregate.py` constructs the exact 512-segment composition
from untrusted source counts; its final theorem requires every imported
segment proof. `run_twin_segments.py` only orchestrates sequential Lean
builds. Neither tool proves the count or extends the kernel trust boundary.

## FW matched-bin supply and physical placement

`Sude.bmor_two_separated_bin_supplies` and
`Sude.bmor_two_matched_bin_inputs` translate the already declared finite
BMOR theta and RS upper hypotheses to separated modulus-two bin stocks,
actual pool membership, ordering and a gap-label range. Their endpoint,
separation and numerical stock hypotheses are explicit. The finite
`Sude.matched_bin_stock_sq_le`, `Sude.matched_bin_stock_after_deletion`,
and `Sude.matched_bins_repeated_after_deletion` formalize FW8's shared
budget and repeated-gap step, including pairs from different bins.
`Sude.select_matched_bin_double_pairs` iterates with disjoint footprints,
and `Sude.bmor_select_and_install_matched_blocks` composes this with
physical installation in explicitly supplied distinct cells. These results
leave FW's actual endpoints, numeric stock and gate checks, physical-cell
capacity, wide-stage error analysis and the rest of the route open. No
additional external assumption has been introduced.
