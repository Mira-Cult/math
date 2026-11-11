# Sude Lean formalization: Lean-checked proof relative to explicit exempt inputs

This directory contains the Lean 4 (`leanprover/lean4:v4.33.1`, Mathlib
`0df444a360eaa60ab8c11dca51a86af692955474`) formalization of **Sude's First
Theorem**, based on delivery revision `965aadb77b4bf4e2487e10fd1e7d7edaf5fb73cc`.
No permanent claim IDs are assigned or changed. The problem statement is in
`../../problems/prime-line-sums/PROBLEM.md`; manuscript and review context are in
`../../problems/prime-line-sums/manuscripts/sude_all_odd_theorem.md` and
`../../problems/prime-line-sums/reviews/sude-all-odd-independent-review.md`.

## Main theorems and trust boundary

`Sude/AllOddTheorem.lean` establishes:

- `Sude.sude_first_theorem`: derives `∀ n, 0 < n → Odd n → Sude.HasSquare n`
  (preserving the exact rank-equivalence semantics of `Sude/Statement.lean`:
  `oddPrime i = Nat.nth Nat.Prime (i + 1)` starting at `3`, `Cell n ≃ Fin (n * n)`,
  and primality of every `rowSum`, every `columnSum`, `mainSum`, and `antiSum`
  with `Fin.rev`).
- `Sude.sude_first_theorem_values`: derives the value-bijection corollary
  `∀ n, 0 < n → Odd n → ∃ b : Sude.Cell n ≃ Sude.pool n, Sude.ValuesValid b`
  via `Sude.hasSquare_iff_values`.
- `Sude.tail_hasSquare`: proves `Sude.TailObligation`
  (`∀ n, 2001 ≤ n → Odd n → Sude.HasSquare n`) from the 15 verbatim published
  analytic hypotheses alone, eliminating `TailObligation` from
  `Sude.compose_finite_and_open_tail`.

This is a **Lean-checked proof relative to the 16 explicitly listed exempt
inputs** documented in `IMPORTS.md` and `import-map.json` — it is **not** an
assumption-free end-to-end kernel proof:

1. `Sude.FiniteWitness` (`0 < n → Odd n → n < 2000 → Sude.HasSquare n`, covering
   the 1,000 positive odd orders below `2000`; `n = 1` is also proved unconditionally
   in `Sude.square_one`).
2. **Rosser–Schoenfeld (1962)**, *Illinois J. Math.* 6, 64–94, pp. 69–70:
   `RSPrimeCountLowerSharp` `(3.3)`, `RSPrimeCountUpperSharp` `(3.4)`,
   `RSPrimeCountLower` `(3.5)`, `RSPrimeCountUpper` `(3.6)`,
   `RSIndexLowerSharp` `(3.10)`, `RSIndexUpperSharp` `(3.11)`,
   `RSIndexLower` `(3.12)`, `RSIndexUpper` `(3.13)`, and `RSThetaUpper` `(3.15)`.
3. **Bennett–Martin–O'Bryant–Rechnitzer (2018)**, *Illinois J. Math.* 62, 427–532:
   `BMORFiniteTheta` (Theorem 1.9 theta conjunct & `(1.18)`, pp. 434–435),
   `BMORProp2_1` (Proposition 2.1 `(2.3)`–`(2.7)`, pp. 438–439),
   `BMORProp2_5` (Proposition 2.5 `(2.10)`, p. 441),
   `BMORProp2_7` (Definition 2.6 & Proposition 2.7, p. 441), and
   `BMORProp4_34` (Definition 3.1 & Proposition 4.34, pp. 451, 478–479).
4. **Montgomery–Vaughan (1973)**, *Mathematika* 20, 119–134, p. 121:
   `MVBrunTitchmarsh` (Theorem 2 `(1.10)`).

No `sorry`, `admit`, custom `axiom`, `native_decide`, `BMORFinitePiFour`,
controller/route premise, target-prime premise, or internal numerical certificate
premise is used. Every `#print axioms` check in `Sude/Audit.lean` reports only
Lean's standard `[propext, Classical.choice, Quot.sound]`.

## Proof architecture across all odd orders `n ≥ 2001`

- **Explicit-formula bridge (`Sude/BMORPublishedExplicitFormula.lean`)**:
  `Sude.bmorExplicitFormulaImports_of_published` proves `BMORExplicitFormulaImports`
  directly in Lean from `BMORProp2_1`, `BMORProp2_5`, `BMORProp2_7`, `BMORProp4_34`,
  and `RSThetaUpper`, including von Mangoldt equivalence (`chebyshevPsiAP_eq_psiAP`),
  imprimitive zero-multiset invariance (`bmorZeroMult_eq_primitive`), functional
  equation symmetry (`bmorZeroMult_one_sub_star`), high-zero summability, and
  finite Stieltjes summation by parts.
- **Band 1 — `2001 ≤ n ≤ 19483` (`Sude/FC2KBandTheorem.lean`, `Sude.fc2k_hasSquare`)**:
  Discharges all 8,742 odd orders using kernel-verified Lucas primality certificates
  for the full FTT target table (`FastFTT`), kernel-verified FPF prefix sieves and
  binary prime-pair profiles, BMOR/RS62 T75 analytic supplies, DQ/RF central
  completion, and `199/200`-expander integral flow routing.
- **Band 2 — `19485 ≤ n ≤ 35733` (`Sude/FWFirstBandTheorem.lean`, `Sude.fw_and_ew_hasSquare`)**:
  Discharges the entire FW and EW regimes (including `Sude.fw_first_band_hasSquare`
  for `19485 ≤ n ≤ 21248`) using the kernel-verified `3,650,551`-pair twin-prime
  certificate (`FastTwinFullPool`), MV73 + BMOR + RS62 five-stage bridge, wide,
  and Brun–Titchmarsh growth constructions, projected CY completion, spare-cell
  diagonal balancing, and common diagonal prime selection.
- **Band 3 — `n ≥ 35735` (`Sude/UpperTailTheorem.lean`, `Sude.upper_tail_hasSquare`)**:
  Discharges all remaining odd orders at unbounded scales via a unified all-scale
  construction (`UpperTailAnalytic`, `UpperTailTargets`, `UpperTailSchedule`,
  `UpperTailGrowth`, `UpperTailWideAndMod`, `EvenIntervalGrid`, `UpperTailTheorem`)
  combining two-phase elementary/Brun–Titchmarsh prefix growth, dyadic bridge
  extension, wide pair blocks, centered all-line midpoint concentration, DQ/RF
  completion, `199/200`-expander routing, and `EvenIntervalGrid` diagonal repair.

## Environment

Lean is pinned by `lean-toolchain`, mathlib and transitive packages by
`lakefile.toml` and `lake-manifest.json`. From this directory:

```sh
lake exe cache get
lake build
lake env lean Sude/Audit.lean
```

The build cache is disposable and is not part of the sources. Run the
repository integrity checker separately from the repository root:

```sh
python3 check.py
```

The repository checker validates repository metadata integrity only; it is not a
mathematical review or a Lean proof. Revision-pinned build and review records are
logged in `RESEARCH_NOTES.md`.

---

> **Historical component notes:** The paragraphs below retain the bottom-up
> descriptions of lower-level modules as originally constructed; obligations
> noted as open at the individual component level are closed in the top-level
> band and all-odd modules listed above.


`Sude.ResidualRouting` proves that, under the cut inequalities, a bounded
flow with some positive unmet demand has a residual path from a positive to
a negative vertex. It proves exact capacity and divergence effects of a
single residual arc and of any supplied simultaneous unit adjustment, and
proves that a successful adjustment decreases integer residual mass by two.
`Sude.SimpleResidualPath` removes loops, proves that the resulting simple
path uses each edge at most once, and constructs its simultaneous unit
adjustment. Thus `integer_flow_of_cut_inequalities` proves bounded integral
flow existence without assuming a path construction. `Sude.PhysicalCutRouting`
combines this with actual row and column network switches. The FC2K variant
requires explicit expansion, demand-box, installed-reservoir and capacity
hypotheses; those inputs and every complete tail route remain open.

`Sude.ReservoirMidpoint` extends a complete even grid through the actual sum
of a sequence of distinct joined gaps and relates the chosen orientation to
the true aggregate midpoint of its low and high entries. `Sude.TargetRouting`
proves the odd parity and zero-total identities needed to route the FTT line
targets, and constructs the public square conditional on the explicit graph,
reservoir, pool-total, diagonal and baseline hypotheses. Those hypotheses
are not established controller conclusions.

`Sude.PrimePrefixSpec` proves that the prescribed pool and its sum coincide
with the odd-prime prefix through its maximum, and that a verified prefix
count, endpoint primality and sum identify the recorded X and T.
`Sude.PrimeSegmentSieve` proves a bounded prime-base trial-division segment
checker correct and proves exact additivity across adjacent segments. Lean
also checks a Lucas certificate for the first recorded endpoint 67,939,607.
Its prefix count and sum, and all other tail-prefix identities, remain open.
The segment checker has not been shown practical at the source's full scale.

`Sude.SieveProgression` proves the source's first-odd-multiple rule and the
exact finite index stride, including the `p²` boundary. `Sude.MarkedSieve`
constructs marked index sets and proves their unmarked candidates are
exactly the odd primes in a segment; `Sude.MarkedPrefix` links a verified
full-prefix count and sum to the pool. This is a finite-set implementation,
not a proof of the source C++ program or a demonstrated full-scale run.

`Sude.FactorSegmentCertificate` verifies a second segment-certificate format:
each odd candidate has either a proper divisor or a prime certified by a
checked Lucas graph. Its proved specification gives the exact prime set,
count and sum. Lean has accepted an actual 54-candidate segment ending at
67,939,607: the half-open interval `[67939501, 67939609)` has seven odd
primes with sum 475,576,967. This does not establish the preceding prefix,
the first tail order's pool identity, or full-scale feasibility.

`firstTailMarked_count_sum` transfers that certified segment result to the
finite-set marking sieve through its proved specification; it does not
evaluate the marking sieve on the tail interval.

`Sude.SegmentedScan` proves that independently checked adjacent marking
segments compose into an exact count and sum, and that a full accepted scan
identifies the pool. Lean has evaluated two separate 512-candidate blocks:
`[3, 1027)` has 171 odd primes summing to 80,187, and `[7171, 8195)` has
112 summing to 859,924. The finite-set test left the intervening candidates
unverified; the separate bitset proof below fills that particular gap. A
one-shot 4,096-candidate finite-set kernel test
was stopped after its observed resident memory reached about 3.8 GB; no
acceptance or full-scale performance claim is made for that test.

`Sude.BitsetSieve` encodes the same marked indices in natural-number bits
and proves the result equivalent to the finite-set sieve. Its executable
base is an explicit list: an earlier set-to-list version got stuck on a
choice-based conversion during kernel reduction. Lean has evaluated a
64-segment bitset scan of the first 4,096 odd candidates and a separate scan
of the next 4,096. A proved one-pass bitset traversal now checks the first
16,384 odd candidates and establishes that `[3, 32771)` contains 3,511 odd
primes summing to 54,056,761. `Sude.PrunedBitset` proves that base entries
with squares at or above a segment's exclusive upper bound can be skipped
without changing any marked bit. Two separately kernel-checked blocks using
this rule extend the result: `[3, 65539)` contains 6,542 odd primes summing
to 202,353,622. The remaining first-tail prefix and all complete tail
routes remain open; the pruning has not been shown to solve full-scale
feasibility.

`Sude.DoublePairStock` and `Sude.DoublePairBatch` prove FC2K5's finite
repeated-difference step, including the `H + 1` count for even differences,
earlier same-side deletions, and a mutually disjoint batch of double pairs.
The pool specialization derives even gaps from actual pool membership and
pays two entries per side for each selected block. A further theorem accepts
the source's real-valued gap window and strict square inequality directly.
Derivation of that window from the controller's concrete endpoints and the
required stock bounds remain open. `Sude.DoublePairPlacement`
installs such a batch in supplied distinct physical cells, preserving the
old reservation, and proves the positive equal-gap identities. It does not
construct the required rectangle geometry or finish either diagonal.

`Sude.FC2KBridge` derives the exact bridge windows, their containment and
cross-gap bounds, the BMOR lower count for both actual pool stocks, and
selection after charging actual reserved entries on each side. The source's
numerical stock and square-gate inequalities remain hypotheses. An admissible
gap preserves an existing complete even grid even when the real controller
radius is only a lower bound for its actual integer coverage.
`Sude.BridgeIteration` proves the source radius update terminates and that,
if every preterminal stage supplies a fresh admissible gap, the resulting
grid reaches X. No stage-by-stage resource certificate is established here.

`Sude.FWBridgeWindowDisjoint` treats the distinct FW source-width windows:
the five nominal real windows overlap on a given side exactly at equal
indices, and the corresponding finite stock overlap indices lie within the
same singleton. Finite stocks can be empty. Actual-stage radius invariants,
stock budgets and batch construction are not consequences of this result.
`Sude.FWBridgeDepletion` additionally proves cross-side disjointness and,
given valid earlier nominal batches, shows their entries add nothing to
either current stock's intersection with an arbitrary initial reservation.
`Sude.FWBridgeFiveBatch` selects all five nominal batches under explicit
analytic, stock-budget and square-gate hypotheses, retaining disjointness
within and across stages. It does not prove the gates, actual grid growth or
physical placement.
`Sude.FWBridgeFiveSequential` also carries these batches through the actual
accumulated reservation and bounds its cardinality at every prefix.
`Sude.FWBridgeNumericalStock` bounds the real stock expression below by
`X/15000` at all five nominal stages under explicit bounds on `X` and its
logarithm; the integer selection gates remain separate.
`Sude.FWBridgeNumericalGates` proves those gates for an empty initial
reservation on the FW range using explicit RS upper and lower hypotheses.
`Sude.FWBridgeFiveEmpty` combines these gates with selection under BMOR and
RS assumptions. `Sude.FWBridgeGridGrowth` conditionally extends a supplied
even grid through `X` using one actual gap from each batch; the initial grid
and physical slot assignment are still required.
`Sude.FWBridgeFiveGrid` composes these results for the same batch witness
and every block index and supplied initial grid.
`Sude.FWBridgeEndpoints` indexes the actual distinct pool entries and links
their block gaps to that grid interface, without assigning physical cells.
`Sude.FWBridgePlacement` installs them in distinct supplied cells or in
arbitrary cells supplied by capacity, without proving controller geometry.
`Sude.FWBridgeSeedIntegration` uses the actual bridge reservation for seed
selection, conditional on the explicitly stated full twin-pair population.
`Sude.FWBridgeControllerSlots` splits every FW endpoint index between the
diagonal and ordinary families; it does not construct their physical cells.
`Sude.FWBridgeRectangles` conditionally installs the diagonal family in
supplied free rectangles. `Sude.FWSeedQuota` reduces seed selection to its
exact candidate quota, which remains an explicit population assumption.
`Sude.FWBridgeOrdinaryPlacement` conditionally installs the ordinary family
while fixing the diagonal rectangles, given suitable disjoint physical cells.
`Sude.FWBridgeJointPlacement` composes both placements on the same square
under supplied compatible geometry. `Sude.FWSeedTraceGrid` derives the
abstract initial grid from sixteen gap-two labels and a supplied growth trace;
the trace and its required coverage are not established there.
`Sude.FWExactWheelWindow` proves the all-`T` exact wheel-window bound under
an explicit periodic enumeration hypothesis. `Sude.FWWheelEnumeration`
constructs that enumeration for every positive wheel, including `W=1`.
`Sude.FWWheelShortPairs` bounds the corresponding `g=2` screened short-pair
charge; it does not establish a pair supply or a growth trace.
`Sude.FWSeedTraceBridgeGrid` composes such a supplied trace with the selected
bridges abstractly; it does not prove physical cross-family disjointness.
`Sude.FWProtectedTraceBridge` establishes growth-footprint avoidance when the
supplied trace reservation contains the bridge and retained values.
`Sude.FWBridgeLayerPacking` packs supplied derangement layers away from the
full rectangle support. `Sude.FWBridgeLayerSlots` reindexes the ordinary
slots into those layers; future layout remains open.
`Sude.FWBridgeLayerPlacement` installs the diagonal and ordinary bridge
entries on the packed geometry under the stated batch and derangement inputs.
`Sude.FWBridgeFivePlacement` selects those batches under BMOR and RS inputs
and installs the same witness in that geometry.
`Sude.FWBridgeCommonFC2K` supplies common derangements for an isolated
bridge placement with the weaker FC2K cut bound. `Sude.FWPermutationExceptions`
formalizes FW's stronger cut-failure event and its finite exception bound;
`Sude.FWPermutationExceptionBound` derives its explicit entropy bound for
unrestricted triples.
`Sude.FWEntropySmallEndpoint`, `Sude.FWEntropyHalfEndpoint` and
`Sude.FWEntropyCurvature` prove the endpoint inequalities and convexity;
`Sude.FWEntropyIntervalGate` combines them on the full large-cut interval.
The subsequent probability and expander steps are described below.
`Sude.FWPermutationLargeCut` connects the interval gate to an explicit
size-weighted fixed-cut probability bound for unrestricted triples.
`Sude.FWSmallCutGate` proves the separate FW small-cut logarithmic gate;
`Sude.FWPermutationLargeUnion` and `Sude.FWPermutationSmallUnion` bound the
unrestricted large- and small-cut unions. `Sude.FWPermutationExpander`
combines these bounds with derangement counting to prove the exact FW cut
inequality for labelled edge occurrences. `Sude.FWBridgeCommonFW` composes
that graph with an isolated bridge placement; later layout remains open.
`Sude.FWSeedRectangleOffset` separates bridge and seed rectangles within one
packing; `Sude.FWBridgeCommonSeed` selects quota-conditional seeds against the
same placed bridge values. It does not yet install the seed values there.
`Sude.FWSeedOffsetPlacement` installs supplied retained endpoints in offset
rectangles under explicit protection and availability hypotheses.
`Sude.FWBridgeSeedDiagonalComposition` composes that installation with the
selected bridge network in one square, conditional on the seed quota.
`Sude.FWRectangleCapacity` proves source-wide RP1 capacity conditional on a
total prefix-stage cap of 270; the actual trace cap remains open.
`Sude.FWSeedLayerPacking` constructs ordinary seed layer geometry away from
the bridge layers under supplied derangements; seed-value installation remains.
`Sude.FWSeedOrdinarySlots` maps all retained seed roles to disjoint
rectangle and ordinary slots, under explicit packed-layer hypotheses.
`Sude.FWSeedOrdinaryPlacement` installs supplied ordinary seed endpoints while
fixing the specified prior cells and selected seed corners.
`Sude.FWBridgeSeedFullPlacement` composes the bridge and all retained seed
placements in one square under explicit analytic, seed-quota and capacity
hypotheses; growth and later stages remain open.
`Sude.FWBridgeSeedWideProtected` adds wide supply while preserving those
entries under further mean and RS assumptions; wide cells are arbitrary and
are not shown compatible with the later FW layout.
`Sude.FWWideSpatialReservation` distinguishes avoiding spatial cells from
preserving their existing entries; the latter has an additional explicit
deletion-budget hypothesis.
`Sude.FWWideRectangleOffset` separates wide rectangle labels from bridge and
seed labels in a shared packing under explicit capacity assumptions.
`Sude.FWWideLayerPacking` packs wide ordinary layers after supplied bridge and
seed geometry. `Sude.FWWheelCommonGap` obtains a disjoint common-gap family
from an explicit pair-population bound; it does not prove that bound.
`Sude.FWWidePhysicalSlots` maps wide roles into supplied geometry, and
`Sude.FWWheelStockGate` derives the wheel pair gate under explicit stock and
pair-count assumptions.
`Sude.FWWheelPairSupply` derives the required pair count from binned stock
under explicit numerical hypotheses. `Sude.FWWideSelectedPlacement` installs
supplied wide blocks in supplied role geometry while preserving prior cells.
`Sude.FWPermutationLargeBudget` places the large-cut union below the strict
`1/189` numerical budget throughout the FW range.

`Sude.BridgeDepletion` bounds each side's loss by the initially reserved
entries in that window plus the selected entries from overlapping earlier
same-side windows; opposite sides are proved disjoint. `Sude.BridgeStageSequence`
selects all stages in order while preserving the actual accumulated
reservation. `Sude.BridgeWindowOverlap` derives this budget from the source's
geometric window overlaps. `Sude.BridgeChosenGrid` then extends each initial
grid through X using gaps read from the selected actual-pool blocks; all
selected stages have disjoint entries. The per-stage numerical budget and
square gate, initial grids, physical cell assignment and rest of the
controller remain open.

`Sude.BridgePhysical` connects those actual selected blocks to a square
permutation. It proves all stage/block/endpoint entries distinct and in the
prescribed pool, preserves initially reserved cells, and installs the entries
in distinct unreserved cells. A total-capacity inequality supplies those
cells; the positive equal-gap equations use exactly the gaps from the grid
proof. `select_grow_install_bridge_stages` composes selection, grid growth
and this placement under explicit analytic, numerical, initial-grid and
cell-capacity hypotheses. The assigned cells are not yet shown to have the
row, column and diagonal geometry required for the controller.

`Sude.BridgeRectangles` installs an injectively selected subset of bridge
blocks into the actual RP1 diagonal rectangles, keeping the other selected
bridge entries available. `Sude.PackedTradeSequence` proves the exact row,
column, both-diagonal, center, and reserved-cell effects of any duplicate-free
sequence of these rectangle switches, and compares two orientations for
signed changes. The rectangle-selection maps, packing and reservation
hypotheses remain explicit in the generic theorem. `Sude.BridgeRectangleAllocation`
constructs the bridge selection maps from explicit block and packing bounds,
with exactly `2d` rectangles per diagonal at each stage, while preserving the
choices of other rectangle families. The rectangle-specific results do not
themselves place ordinary bridge pairs or establish numerical controller conditions.

`Sude.BridgeOrdinarySlots` allocates the remaining bridge double blocks to
the two ordinary networks without reusing diagonal entries. For FC2K's
`d=6`, `Q/2 = 24 + 3n` blocks supply 24 diagonal blocks and `6n` ordinary
pairs per stage. `Sude.BridgeOrdinaryNetworks` reindexes the actual pool
values into the two physical network placements and proves their positive
even gap equations. `Sude.PackedRectangleLoads` and
`Sude.BridgeNetworkAfterRectangles` connect the RP1 two-cell-per-line bound,
diagonal placement and both ordinary matching passes in one square. Subsequent
diagonal switches, including signed changes between two orientations,
preserve every ordinary network cell. Derangements, cut
expansion, numerical gates, prior reservations and the complete controller
remain open inputs.

`Sude.BridgePhysicalGrid` transports each selected-gap grid to the finite
stage and edge labels of the installed ordinary pairs, with exactly one pair
per stage. It also defines repeated permutation layers and proves that the
same edge has the same endpoints at every stage. The grid still starts from
an assumed initial reservoir. `Sude.BridgeJoinedGrid` joins that reservoir to
the bridge pairs when its cells were reserved, proves disjointness and common
endpoints for all edge blocks, and builds the `CenteredNetwork` interface used
by the integral-flow proof. Existence of the initial reservoirs, the full
joined bridge construction, and the controller's numerical conditions remain open.

`Sude.PrefixPhysicalGrid` applies the finite binary-prefix grid to injected
physical pair labels, proving complete and mutually disjoint edge reservoirs
with the required endpoints when the corresponding pair gaps and endpoints
are supplied. `Sude.PrefixPairAllocation` allocates 48 pairs per stage to
24 diagonal rectangles and 6n pairs to both ordinary networks in the FC2K
case; it places the supplied actual pool entries in one square while
preserving reserved cells. `Sude.PrefixInstalledNetwork` turns the installed
layers into complete physical edge grids. These results assume the FPF
population, its exact gaps and disjointness, repeated graph permutations,
and the geometric and numerical packing conditions; they do not certify
the FPF populations or complete a controller.

`Sude.PrefixPopulationCoverage` proves that the allocation exhausts the
retained endpoints when the source count is exact. The values in its
installed cells equal the full retained population, whose cardinality is
`2QP`; this supplies the full deletion set needed by later selections.
The existence and kernel certification of that population remain open. `Sude.PrefixTruncation` restricts any supplied globally
injective full profile to its first `6(n+8)` pairs per stage, preserving its
gaps and endpoint values; it proves the exact retained count and that suffix
endpoints remain unreserved. The full profile and its cross-stage injectivity
are still hypotheses, not results of this truncation.

`Sude.FinitePrefixPoolBound` uses the existing Rosser–Schoenfeld index
assumption and proved rational log bounds to place every odd prime through
60,000,000 in the pool for `n ≥ 2000`, through 74,000,000 for `n ≥ 2400`,
and through 1,800,000,000 for `n ≥ 10000`. These cover the L, C27 and T
source endpoint ranges without proving their separate prime-prefix counts.
`Sude.PrefixThetaCount` uses the existing BMOR theta assumption and the same
RS index assumption to prove upper prime-count bounds at 150,000,000 and
450,000,000. Together these results place **all five** FPF endpoint ranges
in the prescribed pool on their full source domains, as expressed by
`Sude.fpf_profile_prime_in_pool`; no finite prime-count certificate is used
for that membership step. The exact FTT pool count and sum remain separate.
`Sude.GeneratedPrefix.FirstFamilyPairs` kernel-checks 305 Lucas nodes and
the 96 distinct prime endpoints of the first two retained pairs in each of
the 24 L stages. These values come from the hash-matched source stream;
the stream match is provenance, not a Lean proof of the source selection.
`Sude.GeneratedPrefix.L8` expands this to the first eight retained pairs in
each stage: 192 pairs and 384 distinct prime endpoints, using 1,652
stage-local Lucas nodes. The remaining retained pairs and complete
populations remain unverified.
The retained two-pair-per-stage module was sampled at about 3.7 GB resident
memory during one build. An exploratory four-pair-per-stage kernel check
finished with a sampled resident size around 3.0 GB, but no larger fixture
was retained and these observations do not establish full-scale feasibility.

`Sude.FiniteDistinct` replaces quadratic pairwise comparisons with a
kernel-evaluated bit trie. Acceptance implies injectivity; insufficient
bit depth can reject distinct values, so this checker is intentionally
one-sided. `Sude.FiniteDistinctChunks` proves that successful trie state
transitions compose to global distinctness, including across chunks.
`Sude.GeneratedPrefix.L32Distinct` kernel-checks 24 source-slice checkpoints
and proves the first 32 pairs per stage have 1,536 distinct endpoints.
`Sude.GeneratedPrefix.L32Primes` separately checks those endpoints' primality
using 5,037 stage-local Lucas nodes, establishes their source gaps, and puts
them in the prescribed pool under the existing RS lower-index hypothesis.
These 768 pairs are only a small part of the retained population. The library merge-sort route was
abandoned because its well-founded implementation did not reduce under the
kernel checker. Checkpoint states are defined by earlier insertions, so
their full-scale memory and time costs have not been established. One L32
primality stage was sampled at roughly 3.1 GB resident memory during its build.

`Sude.PrefixL64` extends the same source slice to the first 64 retained
pairs in every L stage. It composes the old and new trie checkpoints to
prove all 3,072 endpoints distinct, checks the added endpoints with 5,154
stage-local Lucas nodes, and exposes a single 64-pair-per-stage pool-value
interface with exact gaps. These 1,536 pairs remain a small fraction of
the source population: at `n=2001` the controller requires 12,054 pairs
per stage. No full-population feasibility or controller conclusion follows.

`Sude.PrefixStageCertificate` proves that independently Lucas-checked,
sorted blocks compose across strictly separated ranges and yield an actual
same-gap pool matching. `Sude.GeneratedPrefix.LStage0.All` checks all 452
blocks and 14,448 retained pairs in L stage zero. Under the explicit
Rosser–Schoenfeld lower-index premise and `n ≥ 2000`, these give 28,896
distinct endpoints in the prescribed pool, all in pairs of gap two. This is
one stage only; the other 23 stages and cross-stage separation remain open.
Regenerate these untrusted source literals with
`python3 scripts/generate_fpf_l_stage0.py --chunks 452`; Lean rechecks every
block during `lake build`.

`Sude.PrefixStageIndex` preserves source-list order when turning a certified
matching into injective pool-valued pair labels. `Sude.PrefixStageFamily`
assembles stages only when their endpoint footprints are explicitly proved
disjoint. For `2001 ≤ n ≤ 2400`, `Sude.GeneratedPrefix.LStage0.install_certified_stage`
installs the actual first-stage prefix in the 24 rectangle slots and both
disjoint physical networks, proves the exact supplied entry in every slot,
and accounts for all `2 * 6 * (n + 8)` used entries. The only analytic input
to this result is `RSIndexLower`. It is a one-stage installation: its radius
is insufficient for the controller, and it neither separates nor certifies
the other stages. A direct indexed proof initially caused large elaboration;
an irreducible name for the same checked list prevents that expansion without
changing the certified list or extending trust.
The direct attempt was stopped after about 53 seconds and a sampled resident
size of 4,673,808 KiB; it produced no theorem. The retained interface uses
the proved equality to the accepted list and builds successfully.

`Sude.GeneratedPrefix.LStage1.All` accepts all 14,448 source pairs of
gap four in 452 blocks, with 93,899 local Lucas nodes. The source generator
reproduces them using `--stage 1 --chunks 452`. The prior `AllFull` aggregate
also built successfully before this checkpoint was promoted. The proved range
bounds separate every endpoint from all 14,448 checked gap-two stage-zero
pairs. `Sude.GeneratedPrefix.actualFirstTwoStageFamily` and
`actualFirstTwoStageValues` assemble both accepted stages into a globally
injective, source-ordered pool-value family for the L band.

`Sude.GeneratedPrefix.LStage2.All` likewise accepts all 14,448 gap-eight
pairs in 452 blocks with 94,974 local Lucas nodes. The full aggregate passed
before promotion, and `--stage 2 --chunks 452` reproduced every checked
block. The proved ranges separate its endpoints from both preceding stages.
`actualFirstThreeStageFamily` and `actualFirstThreeStageValues` assemble the
three accepted stages as distinct, source-ordered values in the prescribed
pool, under the explicit prime-index input.

`Sude.GeneratedPrefix.LStage3.All` accepts all 14,448 gap-sixteen pairs in
452 blocks with 96,668 local Lucas nodes. Its full aggregate passed, and the
generator reproduced every block. The verified ranges separate these endpoints
from all three earlier stages. `actualFirstFourStageFamily` and
`actualFirstFourStageValues` join the four checked stages under the same
prime-index input.

`Sude.GeneratedPrefix.LStage4.All` and `LStage5.All` each accept 14,448
pairs, at gaps 32 and 64, with 96,493 and 99,074 local Lucas nodes
respectively. Both full aggregates passed, and regeneration reproduced every
block. `actualFirstSixStageFamily` and `actualFirstSixStageValues` join all
six stages with pairwise disjoint footprints under the same prime-index
input. The remaining 18 L stages and a complete controller remain open.

`Sude.FC2KExpansionGate` proves the source's FC2K1 large-cut numerical
inequality for every real order at least 2001, the conditioned small-cut
inequality, and both source entropy endpoint inequalities. The proofs use
natural logarithms, rational estimates and mathlib's proved enclosures for
`log 2` and `log 3`. `Sude.FC2KEntropyCurvature` proves the first and second
derivative formulas and strict positivity of the source curvature, yielding convexity and the
same entropy bound throughout `[1/256, 1/2]`. The graph-existence proof is
completed by `Sude.PermutationExceptions` below.

`Sude.PermutationConditioning` proves the derangement fraction is at least
one third for every `n ≥ 2`, using mathlib's exact recurrence. It gives an
actual triple of derangements outside two possibly overlapping failure sets
when their combined cardinality is below one twenty-seventh of the finite
uniform sample space. The cut-failure budgets are proved by the modules below.

`Sude.PermutationCuts` connects permutation triples to the routing cut
interface, retaining each edge occurrence. It proves crossings equal twice
the outgoing count, reduces bad cuts to their smaller side, and derives an
expanding triple of derangements from an explicit combined failure-set count.
The two required cardinality bounds are proved by the modules below.

`Sude.PermutationSampling` proves the exact uniform image law for any
family of same-sized subsets and the hypergeometric outgoing-edge count
for a fixed cut and one uniform permutation. Its factorial/binomial identity
uses the genuine without-replacement sample law. The modules below extend it
to three counts and the union over cuts.

`Sude.PermutationJointLaw` proves the product law for independent whole
permutations and the exact fixed-cut failure count as a finite sum of three
hypergeometric terms. It connects the total outgoing counts to the labelled
routing cut, including strict inequality at the integer boundary. The modules
below bound the sum and combine all cuts.

`Sude.PermutationCutUnion` groups exact fixed-cut failure counts by cut size
and proves the small- and large-cut union bounds using `choose n s` subsets.
The counts come from the exact hypergeometric sum, and the events need not be
disjoint. An expanding derangement triple follows if two explicit finite sums
meet the source budget; both bounds are proved below.

`Sude.BinomialEntropy` derives the binomial coefficient entropy bound and
the lower-tail entropy bound from the finite binomial expansion, with exact
endpoint cases. The FC2K exception count follows at its rational threshold.
The containment and summed cut estimates are proved by the modules below.

`Sude.BinomialMode` proves the exact adjacent-term recurrence, mode at
`k` for parameter `k/m`, and the source G2 lower entropy bound with its
`m+1` factor, including both endpoints. The large-cut entropy maximization
and probability estimate are proved by `Sude.PermutationEntropyMax` below.

`Sude.PermutationEntropyMax` proves the three-count Jensen bound, the
hypergeometric numerator estimate, and the complete large-cut integer budget
for every `n ≥ 2001`. It combines the exact finite counting law with G2 and
the established entropy interval and decay bounds. The small-cut budget and
graph existence are established by
`Sude.PermutationExceptions` as described below.

`Sude.PermutationContainment` proves the exact fixed-image containment count
and the falling-factorial power bound, then combines them for independent
whole permutations. The proof retains sampling without replacement within
each permutation. The exception-pattern union is proved in
`Sude.PermutationExceptions`.

`Sude.PermutationExceptions` covers each failed small cut by its actual
outgoing exception pattern, proves the exact retained-input and pattern counts,
and sums the resulting geometric bound. Combined with the large-cut budget
and derangement conditioning, `Sude.fc2k_permutation_expander_exists`
constructs three derangements with the exact routing expansion for every
`n ≥ 2001`. It does not discharge the remaining controller inputs.

`Sude.fullPrefix_realizes_demands` takes an explicitly supplied 24-stage
globally separated L family and, for `2001 ≤ n ≤ 2400`, discharges the
rectangle and layer packing conditions and connects the installed entries
to integral routing. It retains the actual binary-prefix radius, a
parameterized demand bound and their numerical inequalities. For example,
Lean checks these inequalities for radius parameter 2000 and demand bound 994.
The 24-stage family, target proximity, prime diagonals and probabilistic
completion are not established by this theorem.

`Sude.CentralWindow` and `Sude.CentralStock` prove the single-batch CC2
selection from actual two-sided unused stocks: a distinct subset of the exact
requested size has sum error at most `η` from the current mean. The empty
batch needs no interior-mean condition. The proof sorts the finite stock,
checks its two distinct outer counts, and uses an exact sliding-window
crossing; it does not treat entries as independent samples. The labelled
version applies to distinct prescribed entries. Separate lemmas prove the
stock loss under arbitrary prior deletions and the exact update of the mean
from the actual remaining set. The numerical stock supplies and the full
completion theorem remain open.
`Sude.central_batch_select_and_update` composes selection, deletion and the
mean identity for one batch, including the positive remaining-count check
and the bound `η / remaining.card` on the change of mean.
`Sude.central_source_diagonal_batches` proves the three successive selections
under CC1--CC2's quadratic stock-size and two-sided count hypotheses. It
selects the center once, permits empty diagonal batches, charges previous
deletions against each stock, keeps the mean bracketed and retains at least
`n² / 2` entries. `Sude.central_source_batches_with_total_error` also proves
the CC10 signed total deviation of all three batches from the original mean
is at most `3η`, retaining each changing mean and each exact batch size.
`Sude.central_source_batches_with_diagonal_errors` also proves the two CC11
bounds `2η` and `201η/100`, including the shared center and the exact mean
changes. `Sude.central_place_odd_diagonals` places those distinct entries in
the actual unreserved cells of both diagonals, proves their intersection is
the single center, preserves every reserved cell, and proves those bounds for
the full diagonal sums. It assumes the center is unreserved, the supplied
unused stock avoids all reservations, and the explicit stock and mean bounds.
`Sude.central_place_odd_diagonals_exact_pool` instantiates that stock as the
exact complement of reserved cells in the prescribed pool, derives its size
from the reserved-cell count, and proves that the remaining pool is exactly
the old stock with the three selected batches deleted. It also proves the
`3η` combined deviation and the exact mean update and corresponding mean
shift bound for that remaining pool. The numerical
stock-count inequalities and the remaining parts of off-diagonal completion
remain open.

`Sude.RegularFactorMatching` proves the matching-decomposition part of RF1
for a supplied regular set of actual cells. Double counting gives Hall's
condition, removing a matching lowers every row and column degree by one,
and induction gives exactly `k` pairwise-disjoint perfect matchings whose
union is the factor. `Sude.regularMatchingSlotEquiv` identifies every factor
cell bijectively by matching and row. `Sude.sorted_regular_factor_completion`
places the exact unused pool in sorted matching blocks when the entire
unreserved set is a supplied positive regular factor. It preserves reserved
cells and both diagonals and proves row and column errors strictly below the
unused pool's supplied width, relative to fixed entries plus the remaining
pool mean. The central-stock supply and remaining source mean and capacity
estimates are open. `Sude.dense_factor_source_cuts` proves RF1's
cut inequality for every physical row/column cut under the source's degree
bounds and `ceil(Δ/2) ≤ r`; it retains the natural subtraction condition and
handles the opposite ordering by transposition. `Sude.directed_unit_flow_of_cut_inequalities` constructs an integral
zero-or-one flow from all directed cut inequalities, by residual paths and
terminating unit augmentations. Connecting that flow theorem to RF1's physical
row/column cuts and extracting the regular factor are proved in
`Sude.dense_residual_regular_factor`. `Sude.dense_central_stock_completion`
composes that factor with central-stock placement and sorted completion,
under explicit source degree, positive-factor, stock-count and pool-width
hypotheses. It proves error `X + 2t·radius` with
`t = Δ + ceil(Δ/2)`, preserving every old reservation, both diagonals, and
the exact pool. `Sude.balanced_residual_central_completion` derives the RF3
factor degree and residual degree bounds from the actual reserved-cell
occupancies and uses the largest prescribed prime as a strict width bound. It
proves the source's `(1 + 2(9b+6)ε)X` row and column error under the
explicit central-stock count; occupancy, stock supplies, original-mean
comparison and prime line targets for the controllers remain open.
`Sude.bmor_central_stock_full_reservation` derives a bounded central-stock
count from the explicit BMOR and RS hypotheses, charging every reserved
value. `Sude.bmor_balanced_residual_completion` composes that count with the
physical completion under explicit interval and numerical gates. This full
reservation charge is more conservative than the source's optimized deletion
budget; neither gate has been verified for a complete controller.
`Sude.central_window_avoids_outer_bands` proves the source's geometric
separation, and `Sude.bmor_central_stock_source_bound` proves RF10's
`1036/125` lower bound while charging only an explicit bound on reserved
values inside the interval. `Sude.bmor_balanced_charged_completion` combines
that estimate with the physical completion under explicit controller gates.
The actual reserved-family cover, deletion budget and numerical gates remain
to be proved for a controller. `Sude.actual_unused_mean_from_reserved_pairs_source`
proves the corresponding mean-shift estimate from actual distinct reserved
pairs and their midpoint budgets, identifying the original mean with exactly
`T/n²` and using the actual remaining-pool count in the denominator. The
controller's pair classification and numerical midpoint bounds remain open.
`Sude.central_diagonals_from_reserved_pairs` joins this comparison to the
actual central diagonal placement and tracks its subsequent mean shift.
`Sude.central_diagonal_rows_columns_transfer` proves the impact on every
row and column, charging at most `5η/2` plus the exact mean-shift term;
its two-cell line bound includes the coincident center. Controller-specific
stock, occupancy and target conditions still need to be discharged.
`Sude.packed_layers_post_diagonal_occupancy` derives the RF3 row and column
occupancy interval from an actual packed ordinary layer family and explicit
exceptional-support line budgets, including the newly reserved diagonals.
`Sude.bounded_central_construction_from_pairs` composes reserved-pair mean
accounting, physical diagonal placement, charged BMOR central stock,
integral regular-factor completion and both-diagonal/line-error transfer.
Its `PostDiagonalAnalyticInputs` structure explicitly retains the interval,
depletion and numerical gates, required uniformly for any admissible
diagonal placement; the pair supplies, occupancy, those gates and the prime
corrections are still controller obligations. `Sude.post_diagonal_inputs_from_pair_budget`
proves that uniform post-diagonal interface from explicit pair budgets, scalar
endpoint margins and gate, and a cover of the actual reserved values by
accounted entries and shielded outer bands. Its mean estimate uses a proved
floor-safe uniform denominator. The controller must still supply that
classification and verify every numerical condition. `Sude.bmor_two_diagonal_window_supplies`
proves both earlier diagonal-selection stock bounds from the existing BMOR
and RS hypotheses, explicit interval gates and charged deletion budgets. It
counts actual unused entries; the numerical gates remain unverified for a
controller. This is not a tail theorem. `Sude.place_central_exceptions_and_complete_factor` now
selects and places central entries in the actual cells outside a supplied
factor, proves the remaining-pool identity, and completes the factor.
`Sude.central_stock_regular_factor_completion` combines the exact mean shift,
actual physical row and column accounting, and the total exception budget
derived from the row degree bounds. It proves the RF2 error `X + 2t·radius`
relative to the original unused-pool mean, preserving all prior cells, both
diagonals, and the exact pool. The source-specific central-stock and degree bounds remain open.

`Sude.FC2KExpanderPhysical` constructs the same three derangements for both
physical prefix networks, installs the diagonal rectangles and disjoint
row/column pair layers with their exact supplied entries, and proves the corresponding integral routing
interface. Its inputs still include a distinct prescribed-pool pair population,
reservation and packing bounds, and sufficient prefix radius; it does not
establish the controller or a tail route.

`Sude.MVBrunTitchmarsh` states the exact published Montgomery--Vaughan
Theorem 2 (1.10) as an explicit hypothesis, with all positive-domain and
coprimality requirements. `Sude.mv_depleted_neighbour_bound` applies it to
actual surviving same-class primes after arbitrary deletions, and
`Sude.mv_neighbour_radius_identity` proves the source's cancellation term.
`Sude.fixed_gap_half_matching` proves the source's half-edge matching bound
for every positive gap, without primality assumptions.
`Sude.mv_common_gap_from_pair_population` combines the depleted-neighbour
count, common-gap pigeonhole and physical matching under an explicit
candidate-pair population bound. `Sude.sameClassPairs_cauchy` proves the BT2 finite population bound, and
`Sude.mv_common_gap_from_interval_classes` composes actual real-width spatial
bins, multiple reduced residue classes, the short-pair charge, a common-gap
pigeonhole and a disjoint physical matching. It uses an explicit scalar gate
with the exact finite bin count and the floor of the real radius for integer
gaps. `Sude.mv_interval_stage_select_and_deplete` retains exactly `Q` pairs,
proves their physical endpoint footprint has size `2Q`, and removes it from
the actual unused set with exact cardinality. The MV input is used only by
the selected BT prefix phases.
`Sude.mv_interval_stage_from_source_budget` now derives that exact gate from
the source's continuous BT5 budget, proves the positive denominator and floor
transitions, and completes one actual selection-and-depletion stage under the
explicit phase-start and supply conditions. `Sude.mv_iterate_interval_stages`
now proves the repeated physical selection with each chosen gap as the next
radius, exact total depletion and pairwise-disjoint endpoint footprints. It
requires the displayed `BTStageNumericData` for every subset of the initial
stock with the specified stage size and every radius in the stated interval,
together with an explicit stock reserve. This restricted recurrence is not
the source controller's growing-radius phase; see `RESEARCH_NOTES.md`.
`Sude.mv_iterate_growing_interval_stages` implements the source update
`R ← R + gap`, stopping at the target or stage cap, and proves exact pair
depletion and the accumulated final radius. It requires the explicit uniform
`BTGrowingNumericData` condition and a stock reserve; these are not discharged
for any route.
`Sude.BTStageTrace.poolValues` indexes the actual selected endpoints as
prescribed-pool values under an explicit initial-pool containment assumption;
its proved global injectivity covers both within-stage and cross-stage pairs,
and `poolValues_gap` retains each variable stage gap. `Sude.BTStageTrace.install_diagonal_and_ordinary` places these actual
variable-gap entries into diagonal rectangles and both ordinary physical
networks, preserving prior cells under explicit packing, pool and reservation
hypotheses. `Sude.BTStageTrace.physical_seeded_step_grid` proves the complete
grid of multiples of the base gap for distinct supplied pair labels, given a
seed label of that gap and exact identities relating all labels to the traced
stage gaps. `Sude.BTStageTrace.installed_network_step_grid` instantiates those
labels as the actual network pair slots, and
`Sude.installed_variable_grid_endpoints` proves common directed endpoints for
the traced slots and a supplied seed with those same endpoints.
`Sude.BTStageTrace.extend_installed_network_grid` also extends any supplied,
disjoint initial physical grid, matching the source's phase setup. The caller
must still provide the initial grid or a distinct physical seed, and establish
the narrowing to the even correction grid. Controller-specific numerical
conditions remain open. The corresponding `BTGrowingTrace` results now
provide the actual-pool values, physical installation and grid extension for
the growing recurrence. `Sude.bt_shifted_width_identity`,
`bt_shifted_width_lower` and `bt_shifted_radius_growth` prove the algebra of
BT6 and BT8 with explicit positivity and denominator hypotheses.
`bt_phase_entry`, `bt_stage_overshoot`, `bt_linear_phase_bound` and
`bt_phase_target_of_log_budget` prove BT7, the overshoot bound, the general
BT9 logarithmic growth formula and its target implication. Their application
to the concrete phase parameters and all numerical gates remain open.
`Sude.BTGrowingTrace.split_at_stage` and `prefix_stock_accounting` identify
the actual stock after any prefix of selections and its exact depletion;
`prefix_shifted_growth` applies BT8 to the selected stage under its explicit
width condition. `Sude.mv_iterate_growing_interval_stages_with_widths`
retains lower width bounds at each actual stage, and
`Sude.BTGrowingTrace.linear_width_reaches_target` composes those bounds with
the generic BT9 estimate for an actual selected trace. The actual phase data,
stock-floor and paid-budget inequalities remain open.
`Sude.mv_growing_linear_phase_reaches_target` composes the actual selection,
linear-width trace and BT9 target conclusion, including the early crossing
case. It explicitly requires the numerical data for every eligible subset
and radius, a stronger uniform gate than merely requiring them for reachable
states. No concrete phase instantiation has been proved.
The initial ordinary AP phase has a separate elementary short-pair count
(`Sude.ap_short_pair_count`), interval selection and exact depletion, a
growing-radius iteration, and the conditional
`Sude.ap_growing_linear_phase_reaches_target` theorem. It has no
Montgomery--Vaughan premise. `Sude.BTGrowingTrace.append_accounting` joins
successive phase traces at the actual remaining stock, proving endpoint
separation and the total depletion across the phase boundary. The positive
width and uniform numerical conditions and concrete controller instances
remain to be verified. `Sude.BTGrowingTrace.phase_entry_at_stage` proves a
paid BT7 threshold persists at later selected stages under an explicit stock
floor; actually paying each phase-entry threshold remains open.
`Sude.bt_uniform_numeric_data_from_scalar` and
`Sude.ap_uniform_numeric_data_from_scalar` derive the previous uniformly
quantified gates from an endpoint stock bound, a floor pair budget and the
appropriate initial shifted-radius condition. The two
`*_growing_linear_phase_from_scalar` theorems compose those deductions with
actual phase selection and the target conclusion. Their concrete scalar
inequalities remain unproved for every tail controller.
`Sude.mv_continue_after_paid_entry` continues any physical trace that has
paid the BT7 threshold with a BT scalar phase, preserving exact depletion and
cross-phase endpoint separation. Its growth budget is checked against the
paid lower bound, so an actual larger starting radius is accepted. The
controller must still prove the displayed scalar and supply conditions.
`Sude.ap_then_bt_from_scalar` composes the initial elementary phase and the
following BT phase, with a conservative reserve for the second stock and a
budget based on the paid entry target. It proves a single growing trace,
exact depletion and endpoint separation across both phases. The theorem
still requires the actual initial prime supply and explicit scalar bounds;
no selected route has discharged them. The variant
`Sude.ap_then_bt_or_finish_from_scalar` also allows the ordinary phase to
finish when the final radius target is below the BT entry threshold, without
requiring the threshold to fit inside that target range.
`Sude.ap_then_bt_with_minimum_budget` further requires the initial phase to
pay only for the smaller of the final target and BT entry threshold.
The preceding unrestricted matching interfaces do not by themselves prove
the source's midpoint-narrowing requirement. `Sude.narrow_candidate_batch`
and `narrow_matching_and_deplete` now select a `Q`-pair batch of controlled
midpoint width from `zQ` candidates while charging only the kept endpoints.
The AP and BT iterations carry that invariant through every actual stage.
`Sude.ap_then_bt_narrow_with_minimum_budget` composes both narrowed phases,
with the candidate budget correctly using `zQ` and the stock depletion using
`Q`. The initial interval, scalar inequalities, any later-stage supplies and
the complete controller remain explicit obligations.
`Sude.BTGrowingTrace.placed_network_midpoints` transfers the midpoint bound
to actual square cells under the installed-network placement equations.
`Sude.BTGrowingTrace.placed_rectangle_midpoints` does the same for both pairs
of the allocated diagonal rectangles, including their reversed corner order.
`Sude.BTGrowingTrace.packed_networks_midpoints` specializes the bound to both
sets of physical layers returned by the joint network installer.
`Sude.bounded_positive_pool_midpoint_span` derives the necessary half-open
`X/z` midpoint-bin span from positive entries bounded above by `X`, including
the maximum pool entry. `Sude.prescribed_pool_midpoint_span` discharges that
span directly for subsets of the exact prescribed pool with its canonical
maximum as `X`.
`Sude.screened_pool_card` proves the exact `n² - 13` stock after removing
the odd primes at most 43. `Sude.screened_pool_phase_inputs` also derives
the actual post-reservation stock bound, primality, single mod-2 class,
interval and midpoint-bin conditions for the prefix construction. It does
not prove any controller's reservation or numerical budgets.
`Sude.screened_pool_narrow_prefix` composes those facts with the actual
two-phase narrowed selection for `g=2` and `X` equal to the canonical maximum
pool prime. Its `ScreenedPrefixNumerics` fields are explicit internal scalar
obligations, not analytic imports; none is asserted for a controller merely
by providing this interface.
`Sude.BTGrowingTrace.install_screened_narrow` places such selected pairs in
the two ordinary networks and diagonal rectangles, retaining their exact
gaps and midpoint bounds and preserving earlier reserved cells. It assumes
the stated geometry, derangements and capacity bounds; routing and the
controller-specific numerical inequalities are still open.
For the FW route, `Sude.fw_seed_quota_gate` proves the source FW4 quota
uniformly through the largest band endpoint, and
`Sude.fw_allocation_depth_gate` proves its stated base-two allocation ceiling.
These arithmetic gates do not establish the finite twin-prime seed population
or the rest of the route. `Sude.fw_floor_capacity` also proves the source's
lower bound on `floor(n/C)` uniformly throughout a band, with the floor
handled exactly. `Sude.fw_reflected_band_geometry` checks the frozen rational
band geometry and its endpoint-margin coefficients.

`Sude.fw_seed_bridge_disjoint` proves that the bounded FW seed endpoints
are disjoint from bridge entries in the central window when `4 * 2^30 < X`.
`Sude.fw_seed_candidates_after_bridges` combines that separation with the FW
quota to select the exact number of distinct seed pairs after bridge
reservation, preserving matching and prescribed-pool membership. `Sude.fw_poolMaximum_gt_four_seed` proves the needed maximum bound from
the published prime-index estimate throughout the FW range.
`Sude.fw_actual_seed_candidates_after_bridges` specializes the selection to
the prescribed pool, derives pool membership and the matching from primality,
and retains the finite seed population as an explicit internal obligation.
This is not a completed controller.

`Sude.FWNarrowReservation` proves the source NS1–NS4 width and variance
invoice for sixteen narrowest equal-sized groups of actual FW seed candidates.
It handles ties, derives the total range bound from consecutive sorted groups,
and identifies globally distinct physical endpoints in the prescribed pool.
`Sude.sortedSeedMidpoint_range` identifies each computed width with the
actual pair-midpoint span.
Its reservation contains exactly `2 * 6 * (n + 8) * 16` entries; all endpoints
in discarded candidate groups remain available after both reservations.
The finite seed population, allocation probability, cell placement and FW
controller remain unproved; candidate and earlier bridge hypotheses are
visible in the theorem.

`Sude.fw_install_narrow_seed` composes FW's selected, narrowed seed pairs
with the actual rectangle and ordinary-network allocator. In the same
selected family it retains the NS width invoice, exact endpoint reservation,
discarded-group availability, explicit candidate-to-cell identities, both
rectangle-pair orientations, both ordinary-network gap equations, and
midpoint-width bounds for those placed pairs. It assumes the finite seed
population, bridge window, derangements, earlier cell reservation, and
physical capacity and availability; it proves neither the source probability
allocation nor the FW controller. `Sude.unchosenSeedEndpoint_not_retained`
also proves that pairs outside the initial candidate set remain unreserved.

`Sude.prefixPhysicalCells_realizes_retained` proves that, when the exact
allocation capacity holds and the rectangle and network placement equations
hold for actual square cells, those cells are distinct and their entries are
exactly the retained seed endpoints. Its bijection covers rectangle corners,
row layers, and transposed column layers together; `fc2k_prefix_pair_allocation`
proves the relevant capacity equality. This is a physical coverage interface,
not a proof of the remaining probabilistic allocation or controller.
`Sude.install_retained_seed_pairs_exhaustively` derives the coverage from the
actual allocator, for the same witness that provides the packing, placement
identities, ordinary-network gaps, and preservation of earlier cells.

`Sude.TwinSegmentSieve` and `Sude.TwinSegmentScan` prove a bitset sieve and
composition theorem for the FT finite twin-prime population. Each segment
uses one extra candidate to include a pair crossing its right boundary; this
credits that pair to the earlier segment, while the published checker credits
it to the later segment. The lower-endpoint intervals are disjoint and their
combined count is proved exact. `Sude.FiniteTwinSeed` states the exact source
set and a 512-segment plan, and `Sude.TwinStreaming` and
`Sude.PrunedTwinStreaming` prove equivalent streaming and pruned interfaces.
Lean kernel-checked an explicit crossing example and the first 16,384 odd
lower-endpoint positions, proving 500 pairs there. The complete 3,650,551
pair count has **not** been kernel-accepted. The separately checked source
segment with lower endpoints in `[2097197, 4194349)` has exactly 12,495 pairs:
`Sude.GeneratedTwinScan.S001All.total`. This is one of 512 segments, not an
acceptance of the complete population. `finiteTwinSeeds_count_of_scan`
and `fw_candidates_of_finiteTwin_scan` keep that acceptance obligation visible;
`finiteTwinSeeds_count_of_partition` permits any exact width partition. This remains an internal tail obligation, not an imported theorem.

`Sude.ActiveTwinBase` proves a second pruning rule: a base entry whose first
mark lies outside the lookahead segment changes no bit and no pair count.
`Sude.FiniteTwinActive` connects any kernel-accepted active-pruned partition
to the exact FT count. The complete acceptance remains unproved.

`Sude.FiniteTwinNewNodes` exports 645 kernel-checked Lucas prime proofs
for the explicit FT base list that were absent from the previously checked
FTT graph. The other 2,867 base primes already occur in that graph. These
individual prime proofs and 55 checked list blocks now assemble into
`Sude.finiteTwinCheckedBase_complete`. Lean derives completeness using the
already checked 3,511-odd-prime prefix count and the list's checked ordering.
This proves the exact base needed by the scanner, but does not prove the FT
pair count. Regenerate the list and nodes with
`python3 scripts/generate_twin_odd_base.py` followed by
`python3 scripts/generate_twin_base_lucas.py`.

The certified base and active pruning also allowed a kernel check of the
last 16,384 lower-endpoint positions, yielding 90 pairs. Together with the
first 131,072 positions containing 2,674 pairs,
`Sude.finiteTwinSeeds_at_least_2764` proves a lower bound of 2,764 pairs
in the full source set. This is a partial certificate;
the required total of 3,650,551 remains open.

`python3 scripts/generate_twin_segment.py 0` generates the first FT source
segment in smaller modules from hash-pinned, untrusted count hints. Lean has
accepted the first two modules; their disjoint lower-endpoint ranges contain
1,521 and 1,153 pairs. Remaining generated segment modules are not asserted
proved until their Lean builds pass.

`python3 scripts/generate_twin_aggregate.py` generates the final 512-segment
composition from the pinned table; the generated module is not proved until
all segment imports and the composition build. The optional
`python3 scripts/run_twin_segments.py --start 2 --end 511` runs generated
segment builds sequentially and stops on a failed check or insufficient
free disk space. Neither generator nor orchestration is part of Lean's trust.

`Sude.PermutationConditionalLaw` proves the exact conditional sampling law
for a uniform finite permutation after any realizable revealed history. The
next output is uniform over the unused values, each such fiber is nonempty,
and arbitrary events and weighted sums satisfy denominator-free counting
identities. A next-value fiber is itself an extended history, so the law can
be iterated without assuming independent draws. The source's algebra for a
weighted reveal, coefficient bounds and last-slot case are also proved.
The later probability modules compose these facts into moment and union
bounds; their source-specific physical incidence hypotheses remain open.

`Sude.PermutationProbability` equips the finite permutation set with the
uniform probability measure. For any realizable history it proves that the
uniform measure on the history is the original measure conditioned on that
history, and translates the exact arbitrary-event count into a conditional
probability identity. The later probability modules prove moment-generating and simultaneous-
success bounds under explicit incidence and numerical hypotheses.

`Sude.PermutationHoeffding` uses mathlib's proved Hoeffding lemma on each
actual conditioned permutation history. It proves the history integral is
the finite-fiber average, identifies the next-value mean with the average of
the unused values, and proves a one-step sub-Gaussian bound centered at that
explicit mean. It also gives the conditional mean of the sum over all
unrevealed weighted slots. The later probability modules supply the conditional-increment composition
and a conditional simultaneous-success argument.

`Sude.PermutationExposure` proves the nonfinal weighted-permutation reveal
increment for actual conditioned histories, including the removed position
and value. For nonnegative weights revealed in decreasing order it proves
the increment coefficient lies between zero and the current weight, and
uses the verified Hoeffding result to obtain the source-form one-step
sub-Gaussian proxy. `Sude.PermutationExposureLast` proves that the last
slot is deterministic and its increment has proxy zero. The later probability modules compose the reveals and stages and obtain
simultaneous allocation under explicit hypotheses.

`Sude.PermutationTower` proves the exact finite tower law for successive
conditional permutation histories and an inequality form for propagating
a uniform bound on all next-history integrals. Each next-history witness
comes from a proved nonempty fiber. The later probability modules prove the iteration and final union bound.

`Sude.PermutationMomentTower` composes the source-form one-step reveal
moment bound with a uniform moment bound on each actual next history. The
proof derives constancy of the reveal increment on each next-value fiber
and uses the exact finite tower; it does not assume independence. The subsequent weighted-induction and stage modules prove recursion,
tail bounds, and a simultaneous-success union bound.

`Sude.PermutationWeightedInduction` proves a complete weighted Hoeffding
moment bound and a two-sided tail bound for one uniformly sampled
permutation, conditional on any realizable history. It reveals remaining
slots in decreasing nonnegative weight order, uses the actual without-
replacement tower, and handles the last value separately. Its proxy is
proved equal to the squared value range times the sum of squared weights,
divided by four. The later stage module combines independent whole-stage permutations and
derives simultaneous allocation. Matching all physical line incidences
and budgets remains open.

`Sude.PermutationStageMGF` constructs the product probability space of
independent whole-stage permutations and combines their proved one-stage
bounds. It proves the exact stagewise range/squared-weight proxy, a
two-sided line bound, and a union bound over labelled events that may
coincide. Given an explicit bound showing the sum of zero-aware strict-
failure probabilities is below one, it proves the existence of a single
stage assignment satisfying every non-strict line error budget, including
zero-proxy cases. The source-specific incidence identities, numerical
budget inequality and application to the physical controller remain open.

`Sude.StageProbabilityBudget` proves the exact natural-logarithm and
square-root budget behind the simultaneous allocation: for `m > 0`
labelled lines and a nonnegative common variance invoice `V`, if each
line proxy is at most `V/4`, there is one stage assignment with every
line error at most `sqrt(V * log(4m) / 2)`. The proof handles zero proxy
and zero invoice explicitly. Establishing the source-specific proxy cap
from complete physical line incidences and connecting the construction
to the controllers remain open.

`Sude.PermutedSeedProbability` connects the simultaneous probability
witness to the physical seed allocator: the same stage permutations are
installed in distinct cells, preserve prior cells, give the specified
network gaps, and use exactly the retained endpoints. Midpoint lemmas
identify both rectangle and network pair values with the actual selected
midpoints. The theorem assumes an explicit squared-weight invoice for
arbitrary labelled slot forms. Proving that those forms are the physical
square-line errors and discharging their source-specific invoice remain
open. That theorem alone chooses geometry after the permutations. The later
`Sude.exists_fixed_seed_layout` proves a single packed geometry accepts
every later permutation, and `Sude.fixed_seed_layout_has_weighted_allocation`
applies the probability bound after geometry and slot weights are fixed.
This is not a completed controller or tail route.

The optional `Sude.FiniteTwinCheckpoint` combines kernel-checked source
segments 0, 1, and 2 with a separately checked high-end interval to prove
`Sude.finiteTwinSeeds_at_least_39614`. This is a partial lower bound, not
the full FT seed-population requirement. It is deliberately not imported
by the default export, to keep its optional certificate rebuild explicit.
The optional `Sude.FiniteTwinCheckpointFour` adds accepted segment 3
and proves the stronger partial bound `Sude.finiteTwinSeeds_at_least_50723`.

`Sude.LayerPacking.ordinary_stage_row_squared_invoice` proves the ordinary
network portion of the source's `3d` squared-weight invoice for each row
and each column: one orientation contributes two from its two incident
pair slots, while the other contributes four from the single pair
containing both line cells. It assumes `d = 2s` for `s` layers of each
kind. Rectangle
contributions, diagonals, and the full physical line-error identities are
not yet proved by this result.

`Sude.LayerPacking.layerRowContribution_midpoint` proves the exact actual
row contribution of a network layer as its incidence-weighted pair
midpoints plus the signed half-gap term, retaining endpoint orientation.
For a common gap the latter term is fixed as pair midpoints are permuted.
The corresponding whole-square and diagonal identities remain open.

`Sude.packedRectangle_row_card_le_two` and
`Sude.packedRectangle_column_card_le_two` count the actual physical
corners of the entire packed rectangle family: no row or column meets
more than two. The proof first shows such a line cannot meet two distinct
rectangles and then injects its corners into two side labels. A separate
nonnegative-weight inequality bounds the squared invoice by four when
total endpoint incidence is at most two. `Sude.rectanglePairWeight_sum_eq_card` now identifies the actual pair-slot
weights with that endpoint count, including the reversed second pair.

`Sude.prefixRectangle_row_pair_invoice` and its column counterpart
restrict this bound to the actual selected prefix pair slots.
`Sude.prefix_row_combined_width_invoice` and its column counterpart group
the physical rectangle weights by stage and prove the width-weighted
`3d * sum R_j² + 4z²` bound when supplied a per-stage ordinary invoice
and a maximum squared width. `Sude.physical_prefix_row_width_invoice` and its column counterpart now
derive the ordinary contribution from the packed layer lists, while
`Sude.prefixStageLayer_networkInput` identifies the corresponding allocator
pair slots and endpoint orientations. The complete line-error identities
and controllers remain open.

`Sude.physicalRowSlot_weighted_invoice` and its column counterpart now
transfer the physical incidence invoice into the actual allocator slot
coordinates. The rectangle and both ordinary-network pair labels are
proved injective into `Fin Q`; extending their weights by zero preserves
the squared sum exactly. `Sude.PhysicalRowColumnProbability` proves
nonnegativity and a simultaneous midpoint-slot bound for all rows and
columns. The all-line extension is described below; completed line-sum
identities remain open.

`Sude.fixed_retained_row_column_allocation` specializes the simultaneous
row/column midpoint-slot bound to actual retained pair midpoints and
installs the same permutation witness into fixed physical cells while
using exactly the retained endpoints. It assumes the selected width cap
and valid packing; it does not prove completed square-line identities.
`Sude.rectanglePairWeight_main` and `Sude.rectanglePairWeight_anti`
verify the endpoint contribution of each actual oriented rectangle pair
to each diagonal. The total diagonal stage invoice and all-line midpoint probability
composition are proved in the modules described below.

`Sude.DiagonalStageInvoice` proves that the source's rectangle choices give
exactly `2d` squared pair incidences on each labelled diagonal per stage.
`Sude.DiagonalPhysicalInvoice` proves the packed networks avoid both
diagonals, including after transposition, and transfers the diagonal
weights to the same injective allocator slots.

`Sude.fixed_retained_all_line_allocation` now gives one permutation witness
controlling all `2n+2` labelled midpoint-slot forms and realizes that same
witness with the actual retained prime-pair endpoints in fixed distinct
cells. The theorem explicitly assumes a valid packing, source diagonal
choices, and a cap on the selected midpoint widths. These are intermediate
hypotheses to discharge inside the construction, not external imports. It
does not establish the identities with the completed square-line errors,
the line targets, a complete controller, or a tail route.

`Sude.FixedRetainedSourceWidth` reindexes the actual
retained midpoint widths to the source's selected-group labels. It derives
the per-stage width cap and all-line midpoint bound from a selected-group
maximum and variance inequality. It remains an intermediate theorem with
explicit packing and source-resource hypotheses; it does not establish
completed line sums or a tail controller.

`Sude.exists_retained_all_line_source_allocation` constructs the packed
geometry and all-line retained-pair midpoint allocation from explicit
supply, source width, derangement, and capacity hypotheses. It preserves
prior cells and uses exactly the retained entries.
`Sude.placedRectangleContribution_midpoint` connects each actual placed
rectangle pair to its permuted midpoint and signed half-gap, including
the reversed second-pair orientation. The full line aggregation, target
compatibility, integral routing, unused-cell completion, numerical
controllers, and final theorem remain open.

`Sude.FWAllLineMidpoint` composes the FW selected
seed theorem with the packed all-line midpoint construction over its stated
19,485–27,555 numerical domain. The theorem explicitly requires the
3,650,551-seed population, suitable derangements, and physical capacity
and reservation conditions. Those are internal obligations, not trusted
imports. Prime targets, routing, completion and the route as a whole remain
open.

`Sude.PrefixPhysicalLineSum` proves an exact identity
for the sum over selected prefix-pair cells on any labelled line: it is the
sum of actual pair midpoint weights and signed fixed half-gaps. Its pair
labels are reindexed bijectively to the real allocator cells. This theorem
only covers the selected prefix cells; residual cells and the center still
need to be combined with it for a complete line sum.

`Sude.PhysicalPairLineSum` and `Sude.LineResidualDecomposition`
prove exact midpoint/half-gap sums over distinct selected pair cells
and split any full labelled line into those cells and the entire residual.
The center is explicitly retained in both diagonal residuals when it is
outside the selected pairs. `Sude.PrefixPhysicalLineSum` specializes the
selected-cell identity to the allocator's bijectively reindexed actual
prefix cells. The probability weights now match actual pair incidences;
the remaining completion and cancellation bounds remain open.

`Sude.PrefixCenterResidual` proves that the actual
packed prefix rectangles and both ordinary networks avoid the odd-order
center, including after transposition. Thus the center belongs to the
residual part of both full diagonal sums; it is not silently discarded.

`Sude.PrefixPhysicalSlotGeometry` proves exact capacity makes the stage
slot map bijective and identifies each rectangle or ordinary-network slot
with its actual physical cells. The weight-to-line identities are proved;
the completion estimates remain under development.

`Sude.PrefixActualLineCentered` now identifies the actual selected prime-pair
sum on each labelled line with the controlled centered midpoint variable,
its exact finite-stage mean, and the signed pair-gap contribution. The
incidence weights are proved to count the actual pair endpoints, including
both diagonals. `Sude.FullLineCenteredIdentity` retains the complete
residual-cell sum. These results still leave the residual completion,
targets, routing, the numerical supply and the full tail open.

The checked twin-scan segments and the separately checked high-end block
prove `Sude.finiteTwinSeeds_at_least_85524`; see the exact source and review
in `RESEARCH_NOTES.md`. The internal FW supply
condition requires 3,650,551; neither the remaining certificates nor a
complete tail route have been proved.

`Sude.fw_uniform_floored_stock_square_gate` reduces the rounded FW square
gate to an explicit real margin that pays for flooring. The real stock has a
checked `X/3500` lower bound under explicit FW-domain hypotheses. The FW10
early-budget margin and rounded gate now follow from the explicit published
RS index hypotheses, including the separate sharp lower estimate; actual
removed-set accounting remains open. The checked
`Sude.fw_reflected_supply_with_floored_stock_of_margin` composes that margin
with physical matched-pair supply under explicit analytic, placement and
reservation hypotheses; see `RESEARCH_NOTES.md`.
`Sude.fw_installed_matched_block_even_gap` supplies the common positive even
gap in `[2X/3, X)` for each matched block under the explicit placement and
geometry hypotheses. `Sude.fw_reflected_supply_with_margin_and_even_gaps`
retains these bounds in the physical supply witness under its explicit
margin and other hypotheses. The sharp-index early-budget composition
derives that margin from the explicit published RS hypotheses and retains
actual deletion accounting as a hypothesis. A separate checked cardinality
lemma supplies that accounting from stated bridge-batch lengths, retained-set
size and removed-set containment. A later checked specialization protects
the full supplied bridge-and-seed value union; preserving the positions of
all pool values follows from the checked protected-cell preimage interface
once those cells are fixed. A checked total-capacity lemma supplies distinct
free cells under an explicit cardinality bound; that bound follows for the
supplied FW10-sized sets and wide-block count. A checked composition installs
the wide blocks and preserves each supplied pool value at its original cell.
It does not establish FW's row, column or diagonal geometry. Separate checked
FW bridge geometry uses the source's `23/462` width and five-stage schedule;
BMOR-derived stock bounds feed a batch selector under explicit numerical
deletion and square-gate hypotheses. Those numerical gates, successive
selection and actual grid growth remain open, as do the source constructions
and grid extension.

`Sude.fw_selected_actual_line_allocation` composes the FW seed-stage witness
with the proved deviation bound for its actual selected prime-pair cells on
every labelled line. Its 3,650,551-pair population and physical resource
hypotheses remain explicit internal obligations. Wide stages, targets,
residual completion and the full FW route remain open.

`Sude.bmor_select_and_install_matched_blocks` connects the explicit finite
BMOR and RS hypotheses to a batch of genuinely distinct equal-gap blocks,
selects them under one shared deletion budget, and installs them in supplied
injective cells while preserving reserved cells. Its separated interval
endpoints, numerical bin stock and gate, and physical cell geometry are
explicit hypotheses. The FW-specific arithmetic, subsequent repairs and
all complete tail routes remain open.
