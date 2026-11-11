# Sude's prime-sum squares: research writeup

This writeup explains the exact-pool square theorem, its mathematical mechanism,
and its correspondence with the accompanying Lean source. It separates the
formal theorem's explicit inputs, conventional computations, source inspection,
and independently repeated verification. Its subject is the original square
problem, not the stronger toroidal, affine-line or higher-dimensional variants.

The proof source is supplied in [formalization/](formalization/), exported from
revision `927a770a92c4fb135498d73e46d8978f27ec081a`. Its upstream Git subtree is
`f0fc5d8e02d94e20dfd3c498b70aee524c7f2b5b`; the export preserves every Lean module
and omits two non-proof commentary/handoff files, as recorded in the manifest.
The proof and reproduction files, rather than
access to the original development repository, are the dependency of this note.
The [source manifest](source-manifest.json) identifies the released bytes.
The mathematical paper is a separate exposition; no paper is needed to read
or reproduce the statements and checks described here.

## 1. The exact-pool problem

Let $p_j$ be the $j$th prime with $p_1=2$, and let

$$P_n=\{p_2,p_3,\ldots,p_{n^2+1}\}.$$

The original square problem asks, for every positive odd integer $n$, for a
bijection from the $n\times n$ cells to $P_n$ such that every row, every column,
the main diagonal and the antidiagonal have prime sums. The sums need not be
equal or distinct. The prescribed pool matters: replacing it by a convenient
set of primes proves a different statement.

The canonical formal definitions are
[`Sude.Statement`](formalization/Sude/Statement.lean).
An arrangement is a rank bijection
`Cell n ≃ Fin (n*n)`; entry rank $i$ is prime $p_{i+2}$. Thus every pool element
occurs once, and no element outside the pool can occur. `HasSquare n` is the
existence of such an arrangement with the required prime sums.
`hasSquare_iff_values` proves that this encoding is equivalent to a bijection
onto the actual values $P_n$, rather than merely asserting an informal analogy.

For $n=1$, the array $[3]$ works and is proved in `square_one`. For even $n\ge2$,
any row sum is even and exceeds 2, so the odd-order restriction is necessary.
This elementary parity observation is explanatory here; the formal endpoint
being reviewed asserts existence only for positive odd orders.

## 2. What the formal endpoint says

The theorem
[`Sude.sude_first_theorem`](formalization/Sude/AllOddTheorem.lean)
proves the all-odd statement **from** the 16 explicitly typed premises listed
below. The companion theorem `sude_first_theorem_values` states the same result
using a bijection onto $P_n$.

The word *relative* describes the Lean boundary: the endpoint takes proofs of
these inputs as arguments. The 15 analytic inputs are named published theorems,
not newly proposed conjectures. A conventional mathematical proof may cite such
theorems. An assumption-free Lean proof must instead supply their formal proofs.
Otherwise it remains a theorem relative to those external inputs.
Likewise, a conventional finite computation and a Lean proof of that computation are different evidence.

### Complete input inventory

The source types below, not these abbreviations, are authoritative. Here
$\pi(x)$ counts primes up to $x$, $\theta(x)=\sum_{p\le x}\log p$, and
$\theta(x;q,a)$ restricts that sum to the residue class $a\pmod q$.
Bibliographic details and primary-source links are in
[the bibliography below](#9-bibliography).

| No. | Lean proposition | Mathematical content and source |
|---:|---|---|
| 1 | `FiniteWitness` | Exact-pool square for every positive odd $n<2000$. This is 1,000 orders; `square_one` also handles $n=1$ directly. |
| 2 | `RSPrimeCountLowerSharp` | $x/(\log x-1/2)<\pi(x)$ for $x\ge67$; RS62 Theorem 2, (3.3), p. 69. |
| 3 | `RSPrimeCountUpperSharp` | $\pi(x)<x/(\log x-3/2)$ for $x>e^{3/2}$; RS62 Theorem 2, (3.4), p. 69. |
| 4 | `RSPrimeCountLower` | $x/\log x<\pi(x)$ for $x\ge17$; RS62 Corollary 1, (3.5), p. 69. |
| 5 | `RSPrimeCountUpper` | $\pi(x)<1.25506x/\log x$ for $x>1$; RS62 Corollary 1, (3.6), p. 69. |
| 6 | `RSIndexLowerSharp` | $j(\log j+\log\log j-3/2)<p_j$ for $j\ge2$; RS62 Theorem 3, (3.10), p. 69. |
| 7 | `RSIndexUpperSharp` | $p_j<j(\log j+\log\log j-1/2)$ for $j\ge20$; RS62 Theorem 3, (3.11), p. 69. |
| 8 | `RSIndexLower` | $j\log j<p_j$ for $j\ge1$; RS62 Corollary, (3.12), p. 69. |
| 9 | `RSIndexUpper` | $p_j<j(\log j+\log\log j)$ for $j\ge6$; RS62 Corollary, (3.13), p. 69. |
| 10 | `RSThetaUpper` | $\theta(t)<t+t/(2\log t)$ for $t>1$; RS62 Theorem 4, (3.15), p. 70. |
| 11 | `BMORFiniteTheta` | $\lvert\theta(y;q,a)-y/\varphi(q)\rvert\le2.072\sqrt{x}$ for $1\le y\le x\le x_2(q)$, $1\le q\le10^5$, and $\gcd(q,\lvert a\rvert)=1$; BMOR Theorem 1.9 theta part and (1.18), pp. 434–435. |
| 12 | `BMORProp2_1` | Smoothed explicit-formula inequality, including its GRH(1), $m\ge1$, $x>2$, $H\ge1$ and $0<\delta<(x-2)/(mx)$ conditions; BMOR Proposition 2.1, (2.3)–(2.7), pp. 438–439. |
| 13 | `BMORProp2_5` | Conductor-$d$ zero count for $T\ge1$: error from $(T/\pi)\log(dT/(2\pi e))$ is strictly below $0.399\log(dT)+5.338$; BMOR Proposition 2.5, (2.10), p. 441. |
| 14 | `BMORProp2_7` | Finite-height GRH verification for primitive conductors $d\le10^5$, at $H(1)=30{,}610{,}046{,}000$ and $H(d)=10^8/d$ otherwise; BMOR Definition 2.6 and Proposition 2.7, p. 441. |
| 15 | `BMORProp4_34` | For modulus $q\le10^5$, critical-strip zeros of height at most $10^8/q$ are on the critical line; above it they satisfy the zero-free bound with constant 5.6 and primitive conductor $d$ in $\log(d\lvert\gamma\rvert)$. BMOR Definition 3.1, p. 451, and Proposition 4.34, pp. 478–479. |
| 16 | `MVBrunTitchmarsh` | For $x,y>0$, positive coprime $k,a$, and $y>k$, the number of primes in $(x,x+y]$ congruent to $a\pmod k$ is strictly less than $2y/(\varphi(k)\log(y/k))$; MV73 Theorem 2, (1.10), p. 121. |

The formal sources are
[`RSPrimeCountImports`](formalization/Sude/RSPrimeCountImports.lean),
[`PrimeIndex`](formalization/Sude/PrimeIndex.lean),
[`FWSharpIndex`](formalization/Sude/FWSharpIndex.lean),
[`BMORFinite`](formalization/Sude/BMORFinite.lean),
[`BMORPublishedExplicitFormula`](formalization/Sude/BMORPublishedExplicitFormula.lean), and
[`MontgomeryVaughan`](formalization/Sude/MontgomeryVaughan.lean).
The special ranges, multiplicity conventions, conductor choices, and complete
formulas in these definitions must survive any later shortening for publication.

## 3. The mathematical mechanism

This section is a guide to the canonical proofs, not a replacement proof of their
quantitative estimates or geometric installation lemmas.

### 3.1 Preserve the pool while changing line sums

Write $T=\sum_{p\in P_n}p$ and $y=T/n$. Every placement has total row sum $T$
and total column sum $T$. Therefore a proposed prime target vector
$(t_0,\ldots,t_{n-1})$ must have **exactly** this total, not merely approximately
the correct mean. Since every row contains an odd number of odd entries, its
sum and every usable prime target are odd. Target-minus-current discrepancies
are consequently even and have total zero.

The construction reserves disjoint prime pairs and rectangles, then permutes
the entries within them. These moves keep the prescribed pool unchanged.
Their differences provide integer adjustment capacity. A placement with all
rows and columns merely close to prime targets is not enough: the flow and
switching lemmas must realize the exact discrepancies simultaneously.

The source proves integral flow from cut inequalities and transfers that flow
to installed physical switches. Expansion estimates and explicit capacity
bounds discharge the cuts. It separately controls the cells left outside these
networks and the effects on both diagonals. These are substantive steps: an
abstract flow cannot repair a square unless its edges correspond to disjoint,
available physical swaps.

### 3.2 Obtain compatible prime targets

The analytic inputs supply primes in suitable intervals and arithmetic
progressions. The target-selection theorems combine those supplies with the
exact-total condition. For example, the lower-band core produces

$$\sum_i t_i=T,\qquad t_i\text{ odd prime},\qquad |t_i-y|\le D.$$

The bound $D$ fits inside the installed network's capacity. The relevant lower
band uses $D=(23/50)X$ when $n\le9299$ and $D=y/400$ when $n\ge9301$, where
$X$ is the largest pool prime. Its core is
[`FC2KSubbandCore`](formalization/Sude/FC2KSubbandCore.lean).
The upper-tail target theorem obtains the narrower radius $D=y/1400$.
These are proved analytic supply routes, not assumptions that suitable target
primes happened to be found by a search.

### 3.3 Repair the diagonals without undoing the routed lines

After row and column routing, reserved rectangle moves provide controlled
changes to diagonal sums while preserving the row/column targets. The proof
bounds the reachable intervals and chooses a common odd prime in the required
overlap. It then realizes the corresponding adjustments through the packed
physical rectangles. Both diagonals share the central cell at odd order, so
the geometry and remaining-cell completion are part of the argument, not two
independent diagonal assertions.

For the lower band these steps appear together in
`fc2k_hasSquare_of_completed_witness`; for the unbounded regime they are
assembled in `upper_tail_hasSquare`. The source retains the separation,
capacity, residual-cell and diagonal-overlap inequalities needed at each step.

## 4. How the ranges join

| Odd orders | Canonical endpoint | Principal ingredients |
|---|---|---|
| $1\le n<2000$ | `FiniteWitness` | Conventional exact witnesses for all 1,000 orders; still an explicit Lean premise. |
| $2001\le n\le19483$ | `fc2k_hasSquare` | Nine verified prefix profiles, 21 checked subband records, analytic target supply, completion, integral routing, and diagonal repair. |
| $19485\le n\le35733$ | `fw_and_ew_hasSquare` | The finite twin-prime seed pool, analytic target and growth supply, physical installation/completion, routing and diagonal repair. |
| $n\ge35735$ | `upper_tail_hasSquare` | An all-scale analytic construction, expanding networks, all-line midpoint control, completion, routing and diagonal repair. |

The source endpoints are
[`FC2KBandTheorem`](formalization/Sude/FC2KBandTheorem.lean),
[`FWFirstBandTheorem`](formalization/Sude/FWFirstBandTheorem.lean), and
[`UpperTailTheorem`](formalization/Sude/UpperTailTheorem.lean).
Their composition in `tail_hasSquare` uses only the 15 analytic inputs.
Composing with `FiniteWitness` covers every positive odd order. The intervening
integers 2000, 19484 and 35734 are even; no odd boundary case is omitted.

The current lower-band source does **not** use a fully verified 8,742-row FTT
Lucas target table. Its nine prefix profiles and 21 parameter records feed
the analytic target route described above. A 3,750-row FTT certificate is also
present as earlier source, but should not be confused with the final proof's
coverage. The review records the documentation correction needed here.

## 5. From published analysis to the internal interface

The theorem `bmorExplicitFormulaImports_of_published` bridges the four named
BMOR propositions and the RS62 theta estimate to the analytic interface used
by the construction. It includes the identification of the arithmetic-progression
von Mangoldt sum, zero-multiset treatment for primitive and imprimitive
characters, functional-equation symmetry, high-zero summability, and finite
Stieltjes summation by parts. The bridge is important because internal numerical
enclosures must follow from the published hypotheses rather than appear as
additional unnamed inputs.

In particular, the final theorem does not take `BMORFinitePiFour`. The finite
theta theorem and the explicit-formula bridge provide a different dependency
route from an older public prime-count normalization. The new route must be
described and cited explicitly; it cannot retroactively change which dependencies
an older frozen proof packet used.

## 6. Verification and the role of this companion

There are three distinct layers:

1. **Conventional finite evidence.** Reconstruct each small-order square,
   enumerate the exact prime pool, and recompute all line sums with exact
   primality checks. The independent replay passed the full finite range.
2. **Internal certificate proofs.** The Lean source supplies
   certificate data and checker-correctness arguments for internal tail
   computations, including prefix profiles and a twin-prime pool. Those
   certificates are internal to the conditional theorem, not extra endpoint
   assumptions. A full exact-source replay is still needed independently.
3. **Analytic imports.** The 15 literature statements are explicit endpoint
   inputs. Their mathematical provenance and translation into Lean must be
   audited separately from an axiom-output check.

The producer reports a complete default-target Lean build and standard-only
axiom output. The checks reported below independently replayed the foundational statement
module and the conventional finite computation, not the full endpoint build.
Calling the
formal result a relative formalization is accurate; calling it an assumption-free
end-to-end Lean theorem at this stage would not be.

The source has no final tail, controller or certificate-validity premise. That
is a statement about the endpoint's type, not a claim that all sixteen inputs
have been formally discharged. The printed axiom set and the full theorem type
must be read together.

## 7. Source and verification record

### Source identity and producer-reported checks

The upstream formalization subtree has 9,185 files (69,887,589 bytes), including
9,153 Lean source files and twenty generator or checking scripts. The export
contains 9,183 of those files, omitting only the running research notes and an
obsolete coordination handoff. It preserves all Lean modules. Together with
the seven-file finite replay, thirteen regeneration inputs and the pinned
Python-version file, the package contains 9,204 original source files
(86,192,269 bytes), plus its packaging helpers and this writeup.
Generated Lean declarations and certificate data are proof source, not compiled
build products. The source manifest records byte identities and package layout.
The retained `handoff/FWPhysicalFloorStock.lean.txt` is unchecked historical
source, not a module in the build.

All internal Sude imports resolve in this source export. The default root has
a static closure of 4,675 Sude modules; the full source tree is preserved rather
than pruned to that closure. All 100 distinct Mathlib imports exist at the
pinned public revision, and the nine dependency repository/commit pairs were
checked as publicly accessible. These static checks are not a Lean build.
The [reconstruction helper](prepare-regeneration.py) verifies the file manifest
and restores original relative paths into a new scratch directory for the
original generators. Its 22 input-manifest source bindings were checked; the
heavy generators were not rerun.

The pinned toolchain is Lean 4.33.1. The mathlib revision is
`0df444a360eaa60ab8c11dca51a86af692955474`; its transitive package revisions are
fixed in [lake-manifest.json](formalization/lake-manifest.json).
The [lakefile](formalization/lakefile.toml) determines the default build targets.

The producer reported a complete `lake build` of 13,381 jobs and an exit-zero
`lake env lean Sude/Audit.lean` at source revision
`8bfff6f4a68576ab1e8f99c278db0439d229f7f4`. The immediately following source
revision supplied here changes only `IMPORTS.md`, `RESEARCH_NOTES.md` and
`import-map.json`. No Lean source changed between those revisions. These remain
producer-reported full-build results, not an independent full build obtained
for this writeup.

To reproduce the formal build in an isolated checkout with the pinned toolchain
and dependencies available, use:

```sh
cd formalization
lake build
lake env lean Sude/Audit.lean
```

[Audit.lean](formalization/Sude/Audit.lean) prints declaration types and axiom sets but does not automatically
reject every unexpected printed axiom. Inspect the full `@` theorem types and
check the axiom output against the allowed set `propext`, `Classical.choice`,
`Quot.sound`. Exit zero alone does not establish that boundary. Do not describe
these commands as independently passed until they have actually completed on
the precise released source.

### Independently repeated finite computation

The conventional verifier and certificate are publicly available as
[verify_finite.cpp](https://github.com/Mira-Cult/math/blob/a4a6bc01786010cdd592227524425f2ec03bc055/notes/sudes-first-conjecture/certificates/verify_finite.cpp)
and [odd-orders-1-1999.bin.gz](https://github.com/Mira-Cult/math/blob/a4a6bc01786010cdd592227524425f2ec03bc055/notes/sudes-first-conjecture/certificates/odd-orders-1-1999.bin.gz).
The C++ verifier has SHA-256
`60fb2cd11de8613780f7ed47abdd2d0a5707114ceaaa83e895b347fd93e058a8`.
Its bytes are identical to the verifier used in the independent replay.

The [strict replay wrapper](finite-replay/code/cutoff2_finite_remainder_squares.py)
and its exact input/source closure are also supplied here. From the package root:

```sh
python3 -B finite-replay/code/cutoff2_finite_remainder_squares.py
```

On 11 November 2026 this wrapper was independently run with Python 3.12.14 and
GNU C++ 14.2.0. It exited zero with
`PASS_EXACT_FINITE_REMAINDER_1_THROUGH_1999` in approximately 67.5 seconds.
It reconstructed all 1,000 odd orders from 1 to 1999, checking 1,333,333,000 cells
and 2,002,000 labelled line sums. The largest pool prime was 67,796,177 and the
largest checked line sum was 68,630,847,793. It used 1,686,341 stored swaps and
26,336,639,789 exact trial divisions.

The wrapper also passed an independent Python oracle on the 51 odd orders
through 101, covering 5,304 line labels, and rejected 20 malformed mathematical
certificates, eight malformed compression cases, 44 metadata attacks and
33 physical-source attacks. The controls included isolated failures on each
diagonal. The smaller Python oracle is not a second independent full-range
verifier.

Certificate identities:

- Compressed bytes: 10,500,031; SHA-256
  `5f8be996b548afac76e276088da5a094e3ff4375075ecea14aec77c71522b27c`.
- Decompressed bytes: 13,522,748; SHA-256
  `c8f41eb90f2a2d6d08428b5eb1d86cb373abf38467996920d9470e75045a40fd`.
- Input-manifest SHA-256:
  `18fa6f8d39c5dd70acbfd3d3bb62ce00b36368bbe4f53603cabcefd83910c783`.

This is an exact finite computation with the verifier, compiler and execution
environment in its trust boundary. It is not a Lean proof of `FiniteWitness`
and does not establish an infinite tail by itself.

### Independently repeated foundational Lean checks

The exact `Statement.lean` has Git blob
`d0167298083c1a7b1e19f5749d100eeff062b1dc`. Matching bytes were freshly elaborated
using pinned Lean 4.33.1 through `lean --stdin`, without importing a previously
compiled local Sude statement module. Added axiom and type queries for
`hasSquare_iff_values`, `square_one` and `compose_finite_and_open_tail` passed;
the axiom sets contained only `propext`, `Classical.choice` and `Quot.sound`.
The composition theorem retained both explicit premises, `FiniteWitness` and
`TailObligation`, as expected.

Separately, `leanchecker --fresh Sude.Statement` successfully checked a
historical cached object whose source matched the present statement file,
together with its transitive dependencies. All nine dependency Git revisions
matched the final lockfile and tracked source was clean. This was a same-kernel
foundational check, not an independently implemented kernel, a fresh build of
the entire project, or a replay of `AllOddTheorem` and the complete audit.

### Source inspection and its limits

Targeted inspection checked the exact-pool encoding, both diagonals, the range
joins, the full endpoint arguments, and the named analytic clauses against the
primary papers. No translation mismatch was found in the inspected clauses.
It did not reprove the analytic literature, rerun its zero computations, or
independently verify every line of all 9,153 Lean files.

The source's historical documentation claims a full 8,742-order FTT Lucas
target table. This is not the implemented lower-range dependency route.
`FTTFirst3750.lean` covers 3,750 orders, from 2001 through 9499. The actual full
lower-range theorem uses the 21 checked parameter records, nine prefix profiles
and analytic target selection identified in Sections 3–4. Some historical prose
names modules absent from the snapshot. The actual source imports, not those
prose names, determine the proof dependency graph.

## 8. Relationship to the older public proof packet

The public repository already contains a conventional
[resolution](https://github.com/Mira-Cult/math/blob/a4a6bc01786010cdd592227524425f2ec03bc055/notes/sudes-first-conjecture/resolution.md)
and [frozen packet](https://github.com/Mira-Cult/math/tree/a4a6bc01786010cdd592227524425f2ec03bc055/notes/sudes-first-conjecture/packet).
That packet and the formal source documented here have different dependency
routes. In particular, this formal endpoint does not take `BMORFinitePiFour`;
it obtains the relevant interface from the finite-theta and explicit-formula
inputs listed above. The correction below concerns the historical conventional
packet, not an additional input to the sixteen-premise formal theorem.

### 8.1 The historical packet is intact

At public revision `a4a6bc01786010cdd592227524425f2ec03bc055`, both archive parts
match their published hashes and live Git blob identities. Their concatenation
is a 16,142,917-byte ZIP with SHA-256
`9f7580594e535deb32421def057438e862db7b6c1bb140c8929c21f7def3a650`.
The archive identifies scientific snapshot
`67647907ad0693631f42c169df61cbe46a13a3ff` and scientific manifest SHA-256
`0d4ca1b97404ad620389a4f4f5adec1d327c0106c55fca2e353c85421735d3fb`.
There is no demonstrated corruption or pre-existing hash mismatch.

Fresh checks passed all 579 member hashes, the all-odd composition's 342
sources, and the tail composition's 333 sources, 7,339 binding edges across
325 distinct files, and 5,937 ledger predicates. A separate targeted check
passed all 8,742 stored FTT rows, 69,609 Lucas nodes and 25,942 distinct target
primes. That check did not freshly enumerate the prime prefixes establishing
the stored maximum and total in each row. None of these results is a full
component replay of the packet.

After reconstructing and hash-checking the ZIP using its public instructions,
the composition checks are:

```sh
python3 -B verify_packet.py
python3 -B problems/prime-line-sums/code/verify_sude_all_odd.py --composition-only
python3 -B problems/prime-line-sums/code/verify_cutoff2_tail2001.py --composition-only
```

The original packet remains a frozen source and review snapshot. The following
correction is a separately stated source route; it does not silently rewrite
that archive or inherit a claim that its corrected argument was included in
the historical review.

### 8.2 A sufficient restricted prime-count input

BMOR defines

$$\operatorname{Li}(t)=\int_2^t\frac{ds}{\log s}.$$

The prime-count maximum printed in Theorem 1.9 ranges over $1\le y\le x$.
For fixed $x>2$, the error diverges as $y\downarrow1$ under this convention,
so that maximum cannot be used literally. The issue is the lower endpoint,
not placement of the factor $\varphi(q)$.

A sufficient replacement for the inspected uses is BMOR Appendix A.3,
equations (A.2)–(A.3), printed p.515, and Table 4, printed p.516.
The $q=4$ row gives $x_2(4)=4\cdot10^{13}$ and the upward-rounded coefficient
$b_\pi(4)=2.253192$. Use the published pointwise computation only on
$2\le t\le x_2(4)$:

$$\left|\pi(t;4,a)-\frac{\operatorname{Li}(t)}2\right|
 \le\frac{281649}{125000}\frac{\sqrt t}{\log t},\qquad a\in\{1,3\}.$$

The appendix also prints lower endpoint 1 in its surrounding statements.
The restriction here avoids that endpoint. It is not an official erratum,
and the published prime-count computation has not been independently rerun.

**Restricted count lemma.** Put $P_o(t)=\pi(t;4,1)+\pi(t;4,3)$, the number of
odd primes at most $t$. For $2\le t\le4\cdot10^{13}$,

$$|P_o(t)-\operatorname{Li}(t)|
 \le\frac{281649}{62500}\frac{\sqrt t}{\log t}
 \le\frac{1367}{250}\frac{\sqrt t}{\log t}.\tag{Q4.1}$$

For $128\le X\le4\cdot10^{13}$ and $2\le t\le X$,

$$|P_o(t)-\operatorname{Li}(t)|
 \le\frac{1367}{250}\frac{\sqrt X}{\log X}.\tag{Q4.2}$$

*Proof.* The two residue classes partition the odd primes. Adding their
pointwise errors gives the first inequality in (Q4.1), and
$281649/62500=4.506384<5.468=1367/250$ gives the second.
For $f(t)=\sqrt t/\log t$,

$$f'(t)=\frac{\log t-2}{2\sqrt t(\log t)^2}.$$

Thus $f$ decreases to $e^2$ and then increases; its maximum on $[2,X]$
is at an endpoint. Since $128>e^2$ and $f(128)=\tfrac87f(2)$, one has
$f(t)\le f(X)$ whenever $X\ge128$ and $2\le t\le X$. Substitute this
in (Q4.1) to obtain (Q4.2). $\square$

### 8.3 Exactly which uses the correction covers

The following manuscript labels refer to the original files under
`problems/prime-line-sums/manuscripts/` in the complete public packet.
Some files are absent from the smaller browsable presentation subset.

- **S18**, `cutoff2_analytic_sub18_band.md`, S18.12–S18.15: apply (Q4.1)
  at $X$ and $X/8$. Its $24\le\log X\le29$ domain keeps both arguments
  in the allowed interval. The coefficient $1367/250$ is unchanged.
- **BG**, `cutoff2_bounded_pool_geometry.md`, BG1 and BG3–BG8: (Q4.1)
  gives the endpoint count, while (Q4.2) replaces the appeal to the printed
  maximum in BG1/BG5's uniform quantile-width argument. In particular, the
  sentence calling that maximum essential is superseded. The coefficient
  $10.936=2(1367/250)$ in BG6–BG8 is unchanged.
- **TB**, `cutoff2_target_below15.md`, TB2–TB7, and **T75**,
  `cutoff2_target_below1475.md`, T75.2: (Q4.1) supplies the mean/index
  count input. Their lower logarithmic scales are respectively 23 and
  $181/8$; the upper scale is 29. The theta and Li-comparison inputs remain
  separate.
- **TL**, `cutoff2_target_local_band.md`, TL7, and **TE**,
  `cutoff2_target_local_extension.md`, TE5: apply (Q4.1) at $X$ and
  $X/8$ in the raw-stock estimates, without changing their constants.

The relevant scales imply $X\ge128$ and $X\le e^{29}<4\cdot10^{13}$,
and each endpoint argument is at least 2. BG6 treats interval endpoints below
2 separately without evaluating Li there. Its comparison involving
$\operatorname{Li}(X^2)$ uses separate Li inequalities, not the bounded
prime-count estimate at $X^2$.

This is a restricted q4 repair, not a validation of every broader-modulus
prime-count assertion in S18.1. The inspected count applications use q4;
other even-modulus entry estimates use theta. The source formula, elementary
lemma and identified uses were independently cross-checked in a targeted
review. That review did not establish every other construction lemma or rerun
BMOR's finite computations.

The historical lower range 2001–19483 uses the full 8,742-row target certificate,
unlike the formal source's analytic-target route. Its middle range joins the
far-wide construction (19485–27553) to the early-wide construction
(27555–35733). The historical tail beginning at 35735 combines further bounded
controllers with a classical unbounded continuation, including McCurley-based
material not in the present formal endpoint's fifteen-input inventory.
The old package therefore provides conventional construction history and
range statements with the count clarification above, not a substitute for
the accompanying exact Lean source and its proof map.

## 9. Bibliography

- **RS62.** J. Barkley Rosser and Lowell Schoenfeld, *Approximate formulas for
  some functions of prime numbers*, Illinois Journal of Mathematics **6**
  (1962), 64–94.
  [Primary-paper scan](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).
  Theorems 2–4 and their cited corollaries, equations (3.3)–(3.6), (3.10)–(3.13)
  and (3.15), pp. 69–70.
- **BMOR18.** Michael A. Bennett, Greg Martin, Kevin O'Bryant and Andrew Rechnitzer,
  *Explicit bounds for primes in arithmetic progressions*, Illinois Journal of
  Mathematics **62** (2018), 427–532.
  [Author-hosted journal paper](https://personal.math.ubc.ca/~bennett/BeMaObRe-IJM-2018.pdf).
  Theorem 1.9 and equation (1.18), pp. 434–435; Proposition 2.1 and equations (2.3)–(2.7),
  pp. 438–439; Propositions 2.5 and 2.7 and Definition 2.6, p. 441;
  Definition 3.1, p. 451; Proposition 4.34, pp. 478–479.
- **MV73.** H. L. Montgomery and R. C. Vaughan, *The large sieve*, Mathematika **20**
  (1973), 119–134.
  [Author-hosted paper](https://personal.science.psu.edu/rcv4/personal/Publications/large_sieve.pdf).
  Theorem 2, equation (1.10), p. 121.

The literature statements, exact formal definitions and the conventional finite
computation have distinct roles. Neither a short bibliography nor a standard-only
axiom report substitutes for their explicit hypotheses and verification scope.
