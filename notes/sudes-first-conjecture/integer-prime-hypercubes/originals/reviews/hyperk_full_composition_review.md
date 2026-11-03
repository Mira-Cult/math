# Independent review of the full fixed-dimension physical composition

Reviewer: `/root/physical_composition_review`. Review date: 3 November 2026.

**Verdict: no blocking mathematical defect found in FC or its deduction
of FP from the separately reviewed kernel and prime-target interfaces.** The
final scientific revision for this review is
`c5cf3d829f83dcc388af6f065d7f9bda66789458`, tree
`faf629e6c7357585720385a36e9a0b3aaf28fb49` (PR83). I read the completed
independent UF and AF/BK reviews before issuing this final verdict and
matched their consumed source bytes to this revision. Their exact scope
and continuity are recorded at the end of this note.

The conclusion within this scope is the requested one: for every fixed
integer `k>=2`, for every sufficiently large odd `n`, the exact first
`n^k` odd primes can be placed bijectively so that **all** full signed-coordinate
line sums are prime. The proof permits a qualitative, possibly ineffective
threshold depending on `k`. It does not give a growing-dimension regime,
every small odd order, shifted shorter diagonals, or prime section sums.

## Authorship, exact revisions and dependency boundary

I did not author the new full composition, uniform real frame, integer
absorber, distributed-kernel synthesis, target construction, resource proof,
author programs or retained inputs. I previously reviewed the axis,
majority and half-coordinate physical results; my authorship was confined
to their reviewer-owned records and controls. The present assignment added
only this note and
[hyperk_full_composition_controls.py](hyperk_full_composition_controls.py).
I changed no author source, claim, retained input or Git reference.

I read the working agreement, research protocol, problem/interface records,
the complete full composition and distributed-kernel synthesis, the consumed
UF and AF statements, and the relevant unchanged PS, U/AP, FS/JC and KPT
interfaces. I recovered each scientific revision into a separate exact
`git archive` and checked principal bytes against `git show`:

1. `c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb`, tree
   `65756bab209c4fd74e32327344942bfc56a1bb25`: original full composition.
2. `c5cf3d829f83dcc388af6f065d7f9bda66789458`, tree above: additive
   clarification of capacity indices and computable packing/resource
   constants, plus a finite partition-count control. UF, AF, BK and the
   earlier component bytes are unchanged.

The first revision had a nonblocking ambiguity about the capacity indices.
Both a spare-envelope interpretation and a shift of the inherited axis
indices satisfied the estimates. The author made the latter explicit in
the second revision: baseline `K_0`, axes `K_1,...,K_A`, partitions
`K_(A+1),...,K_D`. I checked the entire additive diff and replayed the
updated author program. No new proof mechanism or exponent was introduced
by that clarification.

Principal source bindings at the final revision:

| File | SHA256 |
|---|---|
| `manuscripts/hyperk_full.md` | `6c0a5c68259154745edf1bfc459437b9b1744c6eeb4f9df0c184c335367dc721` |
| `code/hyperk_full.py` | `637c0274697ef0590fe030d3f4714df38026d95075f23854ae892be85af0bec5` |
| `manuscripts/hyperk_distributed_kernel.md` | `a0ea6e14b51b2cdd92b4c9da442f1fef3eeeafa26cf3ef3f84dd4290f9c6ac27` |
| `code/hyperk_distributed_kernel.py` | `b05dc1078ba84f7969898abd6d6444249b12d953df0a8fd7316abae0e2535e8a` |
| `manuscripts/hyperk_full_controller.md` | `38de54de8b5e5d751e9d700f689b9417b610019d56e170d47f209c86e2adbec6` |
| `manuscripts/hyperk_reconstruction_alt.md` | `623cae1101615723a9ddc367145675c41d93067ee64502663b56d072059eeeb5` |

The reviewer program enforces these and five inherited manuscript bindings.
Its optional previous-source check enforces all eleven bindings at the
first revision as well. The original full manuscript and program hashes
were, respectively,
`d6c09eea509ae7cb288d87705efdaf4ad4530bed4501ed135135787c20e78da9`
and `22d774bd31f335b8668421db6f0334a4acc72826d19cb8c612572728ab1b401c`.

The integer-image theorem and the analytic target/supply proofs retain
their separately recorded reviews. My earlier physical review checks U/AP
and the original resource substitutions. Here I check their interfaces
and the new logarithmic/replica invoices, not claim a second full review
of the analytic number theory. UF and AF have new, separate nonauthor
reviews. This is conventional internal mathematical review, not journal
refereeing, formal GitHub approval, remote CI or proof-kernel verification.

## 1. The exact residual interface and the finite hierarchy

The target interface consists of odd integer line targets, all
disjoint-block partition identities `C_J y_H=C_H y_J`, the exact directional
total `T`, and distance at most `n^(3/5)X` from the exact pool mean line sum.
The oddness is necessary for odd line length. The unchanged eventual
integer-image theorem supplies precisely the stated compatibility
relations in its stable range; the construction does not appeal to a
rational rank calculation or ignore a residual congruence condition.

Subtracting actual array line sums preserves the identities. For a
collection `pi` of disjoint nonaxis signed blocks, its shared residual
`e_pi` is independent of the block chosen in its definition: the pairwise
partition identity interchanges any two choices, and contractions on the
remaining disjoint blocks commute.

After axes are exact and all partitions with more than `b` blocks are
exact, a `b`-block residual belongs to the full signed kernel on the
complement. A singleton contraction there is zero by an axis identity.
Every larger signed contraction is the residual for the extended partition
`pi union {J}`, already zero. This proves membership in **every** defining
kernel equation, including complementary diagonals and central placements.
The argument remains valid over an arbitrary residue ring.

The hierarchy has exactly `floor(k/2)` partition levels. A structural
partition has `d<=k-2b` free coordinates; only its placements grow with
`n`. The recurrence for `Pi_k` in the clarified source counts all signed
structural partitions, including the empty one. Its values through six
are `1,1,3,11,49,257,1539`; those values are finite diagnostics, while the
least-coordinate decomposition proves the recurrence for variable `k`.

## 2. Complete selector signature and actual switches

In `V=(tensor_H Q_H) tensor N`, each pure selector is supported on a
noncentral positive alphabet, with the prescribed coordinate reflections.
Its entire alphabet is disjoint from every other selector alphabet and
the absolute alphabet of `N`. These are restrictions on actual supports,
not just on their nonzero traces.

A contracted block meeting two tensor groups cannot have a supporting
point. A proper signed block inside a selector has zero contraction by PS;
a wrong full sign pattern has zero contraction as well. A block contained
in the complementary coordinates has zero contraction because `N` belongs
to their full kernel. The only surviving blocks are entire native
selectors with the exact native signs. This proves (F8) for every signed
partition, not merely its native trace.

Thus a level preserves all earlier levels, all axes and every other
partition at the same level. Only proper subcollections of its native
partition can move. At the last level each original nonaxis line family
is corrected. There is no missing middle-size family in dimensions five
or higher.

Every nonzero entry of `V` is `+1` or `-1`. Pairing in one selector
coordinate and holding the other coordinates fixed produces a disjoint
pairing of opposite signs. A distinct actual prime pair with one common
actual gap for the whole stage then realizes exactly that gap times `V`.
This remains true for a signed selector, a central native kernel point,
and the empty complementary tensor. The source does not interpret an
arbitrary integer lift as a physical permutation.

The number of pairs is paid by `M(k)=ceil(S/2)`, using the explicit support
bound in (F11a). Different stages are subsequently made cell-disjoint and
receive fresh endpoints, so their configurations can be selected
simultaneously. The proof requires a common actual gap within a stage;
different stages can have different gaps divisible by the common grid gap.

## 3. Distributed kernels, integral rounding and shared-trace splitting

The BK synthesis uses its two frames in the correct order. The real frame
is fixed before the demand. Rounding its **template coefficients** leaves
an integer full-kernel remainder of cell norm at most half the template
point degree. AF is applied only to that logarithmic remainder. Hence its
polynomial coefficient loss yields the additive `n^d log n` term, not an
`n^d` multiple of the original prime-scale error.

For a real kernel element, the rounded real-frame combination is an
integer kernel element within `O(log n)` in cell norm. This proves the
covering-radius statement used in the composition; AF need not absorb a
noninteger remainder in that argument. Indexed duplicates are counted in
both family size and point degree, and dormant templates are retained.

A shared trace can have size `n^(b-1)E`. The manuscript correctly reserves
`q=m^(b-1)` copies of the entire frame. For `M=e_pi/g`, approximate
`jM/q` by integer kernel elements `Z_j`, with exact endpoints `Z_0=0`
and `Z_q=M`. Differences `M_j=Z_j-Z_(j-1)` sum exactly to `M`, remain
compatible, and satisfy

`||g M_j||_infinity <= 3^(b-1) E + O_k(g log n)`.

Applying BK to each piece gives precisely the three terms in (F14).
No fractional switch is proposed. Choosing nearest integers cell by cell
would fail here, as the reviewer negative control explicitly shows.

All copies are planned before the baseline errors are observed. The
kernel frame and replica geometry are not reselected in response to a
later demand. The number of copies is paid in the reservoir invoice:

`q |N_d| = O_k(n^(d+b-1) log n) <= O_k(n^(k-b-1) log n)`.

Summing finitely many structural types gives `O_k(n^(k-2) log n)`
nonaxis reservoirs, dominated eventually by the existing axis invoice.
This is the point at which the large shared-trace amplification is paid;
the proof does not replace that amplification by an assumed bounded norm.

Complement dimension one is harmless but must be distinguished from the
prime-array theorem's exclusion of `k=1`: its kernel is the zero-sum
kernel of one primitive integer sum row. That row is saturated over the
integers and every residue kernel lifts. Complement dimension zero uses
the stated scalar convention, with physical pairing in an outer selector.

## 4. Packing: local collisions, conditional probabilities and all lines

The two collision estimates are logically distinct and both are needed.
Within the current partition pass, point degree `B` bounds the number of
earlier stages above any native cell by `B q L`. Matching a specified
selector tuple fixes at least one distinct sampled label in each of the
`b` selector alphabets. Its probability is `O_k(m^-b)`. Counting actual
support words gives collision probability `O_k(BL/m)=o(1)`.

This estimate holds uniformly over **all** earlier legal choices in the
current pass; it does not assume that the partially constructed current
pass already satisfies a line cap. That uniformity is what permits the
subsequent conditional concentration argument.

For earlier completed passes, fix a candidate support vertex and condition
on every sampled label except one occurring in that vertex. Varying that
label traces a full signed-coordinate line, with all other coordinates
fixed. Repeated occurrences of the label in several coordinates simply
enlarge its varying block; they do not turn it into an uncontrolled
arbitrary-slope line. Since prior full-line occupancy is `o(n)`, only
`o(n)` possible values are excluded. A candidate uses a fixed number of
labels and vertices, so a union bound applies. Whole-reservoir freshness
also excludes only `O_k(K_D+log^2 n)=o(n)` labels.

Consequently every proposal has legal probability at least one half
eventually. The distribution of its accepted value is the original
injection distribution conditioned on legality, giving the required
factor of at most two on any incidence probability.

I checked all rows of the full-line load table:

| Line's varying block | Native-template incidence used | Result after `q` replicas |
|---|---|---|
| One entire selector block | At most `B` templates at the fixed native cell, probability `O_k(m^-(b-1))` | `O_k(BL)` |
| A proper nonempty subset of a selector block | The same `B` bound, with a fixed coordinate providing an extra `1/m` | At most `O_k(BL)` |
| A nonempty signed block in the native complement | At most `nB` actual support incidences along that native line, probability `O_k(m^-b)` | `O_k(BL)`, since `n/m<=3` |
| A block meeting two tensor groups | No support point, by absolute-orbit separation | Zero |

The complementary-line row counts support even when its signed contraction
is zero. It therefore does not confuse cancellation with physical
occupancy. All central and exceptional sections are included. In
particular the resulting full-line cap also bounds every coordinate
slice: partition a slice into its axis lines. No global-volume estimate
is used to infer a local packing result.

For accepted-stage indicators, conditional moment bounds give the stated
Chernoff estimate without independence between accepted stages. With the
clarified constants, the mean bound is at most `6 C_0 B L`. Since
`e-1<2`, threshold `18 C_0 B L+(k+2)log n` has failure probability at
most `n^(-k-2)` for each line. Multiplying by maximum stage support and
union bounding over `O_k(n^(k-1))` lines proves a successful pass exists.
Choosing such a realization before the next pass supplies its prior-load
hypothesis. There is no circular use of the eventual cap in the
within-pass legality estimate.

Separate prefix, macro and residue passes give their separate invoices.
The clarified factor `100` in the combined load constant includes the
`ceil(32K_j)<=33K_j` macro count. The axis packing theorem is invoked
only after the nonaxis geometry has been fixed with `o(n)` axis load.

## 5. Whole bundles, residues and the unused pool

If `b>=2`, a line meeting a stage fixes a selector coordinate in another
block. Freshness of all selector orbits throughout one scalar reservoir
therefore lets the line meet at most one of its stages. Its change
between the two complementary central states is at most `S X`. For
`b=1`, the native line coefficient is the fixed `N(c)`; the two central
scalar totals differ by at most `g`. The remaining lines satisfy the
claimed range as well. Entire bundles, not cells or individual pairs,
are the independent random choices in JC.

This freshness condition is substantive. The reviewer control constructs
64 cell-disjoint stages reusing one selector alphabet. Two complementary
states have equal central scalar total but a specified line differs by
64 stage gaps. Disjoint cells alone would not bound a bundle's line range.

Every line target and every current line sum is odd. Dividing their even
integer discrepancy by two before reducing modulo `h=g/2` is valid.
AF's fixed integral subframe generates the full kernel over each composite
ring; reducing its coefficients gives representatives `0,...,h-1`.
Actual gaps congruent to two modulo `g` realize exactly twice those
coefficients modulo `g`. No inverse of two, of `n`, or of another
nonunit is used. The same partition hierarchy proves all required
preservation identities over the residue ring. At the end every original
line error is divisible by `g`, and all main switches preserve that fact.
The `O_k(gX log n)` numerical residue drift is separately paid.

There is no dependency on an unknown future error in choosing the common
gap. The FS seed-matching argument can select `g` from the known prime
pool before the `g`-dependent residue slots are planned. The geometric
estimates are uniform for its logarithmic permitted range. This ordering
leaves FS's fresh-endpoint argument and the final unused complement intact.

With the new logarithmic line invoice, joint centering gives (F17).
Every macro cell has its actual pair midpoint as expectation; uncontrolled
prefix/residue cells are paid separately. Summing the reserved error over
one axis partition counts every reserved cell once. Since at least half
the exact pool remains unused, its changed mean differs from the original
mean by at most `2E_0/n`. Expected completed line sums are consequently
within `3E_0`, and the unused bijection has simultaneous fluctuation
`O_k(X sqrt(n log n))`.

I checked both actual complementary bundle configurations with fresh prime
endpoints and an exact unused-mean identity in a finite first-prime-pool
fixture. That fixture is explicitly rejected as an all-prime-line
certificate. The asymptotic existence statement still rests on the
concentration and supply proofs, not that finite permutation.

## 6. The common ledger closes for variable fixed dimension

The clarified indexing has `A=2k-3` axis corrections followed by
`floor(k/2)` partition corrections, with baseline scale `K_0`. Thus
`D=A+floor(k/2)`. Shifting the inherited axis capacities up one index
makes the first cut-flow requirement smaller relative to capacity and
preserves every later positive-gap comparison.

Put `Delta=3/[20(D+1)]` and `eta=Delta/4`. Direct algebra gives

`a_D = 3/4 - 3/[20(D+1)]`,

`4/5-a_D = 1/20 + 3/[20(D+1)]`,

`3/5-a_D/2 = 9/40 + 3/[40(D+1)]`,

`Delta-eta = 9/[80(D+1)] > 0`.

These identities prove the strict margins for every fixed dimension;
checking many dimensions is not their proof. The support/tuple constants,
including the very large pure selectors, are fixed after `k` and `eta`
are chosen and before the ambient order tends to infinity.

The complete endpoint invoice remains
`O_k(n^(k-1)(P_M+g+K_D))`. Even if all previous deletions concentrate
in one requested narrow interval and residue class, its ratio to the
fresh supply has the positive margin `4/5-a_D`, with logarithms absorbed
by that margin. The same margin pays `delta K_D X log n` midpoint bias.
Full-line occupancy is `o(n)`, and whole-bundle fluctuation lies below
the baseline by the displayed square-root margin. The axis rounding
term `g n^(k-1) polylog n` and the kernel absorber term
`g n^d log n`, `d<=k-2`, are negligible in prime-sum units.

At each numerical partition level the required scalar is bounded by
`n^eta` times the preceding line error, plus the explicitly paid rounding
terms. The increment `Delta-eta` dominates every fixed logarithmic factor.
After correction, actual occupied-cell counts bound the next original
line errors by `O_k(K_j X log n)`. Same-level partitions preserve each
other, so the finite number of structural types does not consume another
sequence of exponent increments.

The final target window `mu^(3/5)` is `o(X)` because its power difference
is `k-(3/5)(k+1)=(2k-3)/5>0` for every `k>=2`. KPT supplies the full
partition-compatible odd prime vector with exact total `T`, so it meets
FC's baseline tolerance. Repeated target values do not repeat array
entries: supply and completion use an injection and its exact unused
complement, while all later operations merely switch those same entries.

## 7. Replays, independent controls and evidence limits

Both frozen author commands passed under Python 3.12.14:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_full.py --self-test
```

The original replay had ten partition fixtures, two legal partial prime
trades, sixteen compatible splits, four negative controls, packing
fixtures in dimensions four and five, and symbolic resource diagnostics
through dimension 128. The clarified replay additionally checks the
partition recurrence against complete enumeration through dimension six.

The reviewer controls import **no author code**. They independently build
selectors, contractions, partition enumeration, point-derived full-line
labels, actual prime-pair configurations, compatible splitting and
rejection sampling. Reproduction from the repository checkout:

```sh
mkdir /tmp/hyperk-full-composition-source
git archive c5cf3d829f83dcc388af6f065d7f9bda66789458 problems/prime-arrays-beyond-square | tar -x -C /tmp/hyperk-full-composition-source
python3 -B problems/prime-arrays-beyond-square/reviews/hyperk_full_composition_controls.py --source-root /tmp/hyperk-full-composition-source/problems/prime-arrays-beyond-square
```

An optional `--previous-source-root` points to the analogous original
archive and checks all eleven earlier source hashes as well.

The reviewer program's SHA256 at completion is
`a276693955471cc9728ac6cc61fcaf293f2b390ea95bac7a7ef5aabaa1220d73`.

| Independent control | Outcome |
|---|---|
| Complete geometry inventories | Dimensions 2--6 at order 3, and dimension 4 at order 5; direct cell sets agree with point-derived canonical labels and the exact line count. |
| Independent pure selectors | Alphabet/support counts `(3,4)`, `(13,32)`, `(75,416)`; every signed contraction checked. |
| Partition signatures | Nine variable-shape fixtures through dimension 6; 6,674 exact line/partition equations, including zero native coordinates and mixed signs. |
| Hierarchy | Exact descent in dimensions 4, 5 and 6; composite-ring descents modulo 4, 6, 8, 9 and 12. |
| Integer splitting and residues | Twenty compatible splits with overlapping frame supports; 249 integer-half/residue calculations, including `h=1`. |
| Exhaustive selector injection law | All 20,160 injections of six labels into eight orbits; legal fraction `6187/6720`, whole-block incidence `1/8`, proper-subset incidence `1/28`; accepted probabilities obey the factor-two bound. |
| Multi-pass disjoint packing | Dimensions 4 and 5 at order 49, and dimension 6 at order 43 with 441 replicas. Respectively 1,152, 4,608 and 56,448 distinct cells; complete full-line maxima 6, 11 and 8. |
| Whole-bundle legality and unused mean | Two complementary four-stage prime bundles with 16 and 64 fresh endpoints; an exact first-625-odd-prime permutation audit pays the unused mean and explicitly has a composite line. |
| Resource arithmetic | Exact rational margins for dimensions 2--256, plus the all-dimension algebraic identities audited above. |
| Negative controls | Fourteen rejected failures: wrong sign, insufficient complementary kernel, overlapping orbit alphabets, omitted pair family, cellwise rounding, unpaid amplification, global-volume-only packing, missing bundle freshness, duplicate prime, composite endpoint, wrong residue gap, invalid inversion, fixed exponent ladder and target-vector/arrangement confusion. |

These are finite controls. In particular the packing fixtures do not prove
an asymptotic packing lemma, the exact signature checks do not prove UF
or AF, and no control is a certificate of a full higher-dimensional prime
array. The full conclusion depends on the conventional proofs and the
separate component reviews identified here.

Local `python3 -B check.py` passed all 45 repository integrity/tool tests
after both reviewer files were added. This validates repository structure
and tool behavior, not the mathematical conclusions. The coordinator also
replayed the final reviewer program against both exact archives and
reported a pass; that replay is separate from my proof audit and is not
remote CI.

## Final component disposition

The separate uniform-frame review
[hyperk_uniform_frame_review.md](hyperk_uniform_frame_review.md) is
complete at `c7f22dd8a01d28ab02c832f6c2b8b4145d88b6bb`, with no blocking
defect found. I read its written verdict, quantifier audit, both variance
bounds, physicalization audit and exact-control scope. Its canonical source
bytes are identical at the final composition revision.

The separate absorber and synthesis review
[hyperk_absorber_review.md](hyperk_absorber_review.md) is also complete at
the same original scientific revision, with no blocking defect found. I
read its written proof audit of strict strata, coherent subdivision,
fixed-family point load, maximum coefficients, all-modulus generation,
and both rounding interfaces. Its AF/BK and consumed component bytes are
identical at the final composition revision. The report's SHA256 is
`41300e4de6b46ac964d45b5dd0c42826c751259940368cdb688b275d4e426b76`.

Accordingly there is no outstanding named mathematical lemma in this
review chain for the stated qualitative fixed-dimension conclusion. This
is a completed conventional composition review relying on the separately
reviewed components, not an assertion that one reviewer independently
reproved every component or that finite tests constitute a proof.

| Obligation | Status in this review |
|---|---|
| Full residual interface and descending partition hierarchy | Conventional proof checked; no blocker found |
| Actual disjoint switches, replica packing and complete-bundle ranges | Conventional proof checked; independent finite controls passed |
| Composite residue repair, exact splitting and resource closure | Conventional proof checked; no unaccounted division, amplification or load found |
| Exact first-prime-pool deduction FC -> FP | Conventional composition checked using the separately reviewed component interfaces; no remaining blocker found |
| UF | Written independent review read; canonical bytes unchanged |
| AF/BK | Written independent review read; canonical bytes unchanged |
| Remote CI / proof-kernel verification | Neither performed nor claimed by this review |

Publication and integration remain the coordinator's responsibility.
Historical partial-result reviews are preserved with their original scope;
this new composition and its source pins must be cited for the all-line
conclusion.
