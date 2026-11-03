**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/reviews/hyper4_analytic_review.md).

# Independent analytic and prime-target review, dimension four

Reviewer: `/root/hyper4_analytic_review`.

Reviewed scientific revision:
`b837e307fc41975d0fb332c8215d6835ba47a271` (private PR81).
Review performed 2 November 2026. This note is an actual nonauthor review,
not a formal GitHub approval, kernel verification, remote CI result, or
coordinator integration decision.

## Verdict and authorship boundary

**Accepted within the analytic/target scope below. No blocking mathematical
finding remains in that scope.** I did not design or author any of the new
reviewed sources, and I examined them after the stated revision was frozen.
The inherited conversation contained author discussions; those discussions
were not taken as evidence in place of reading the source and imports.

The accepted obligations are the weighted completion lemma HW, set-pattern
compatibility lemma HP, SPT4's analytic target construction, and the fresh
prime-pair supply in U4 Section 2 under its stated global deletion allowance.
I checked the quantitative interface between those obligations. SPT4's odd
integer-lift conclusion additionally uses the separately reviewed SI4 image
theorem. This review does not independently certify SI4's full compatibility
proof, AP4/EP4's support packing, the physical permutation realization, or
the final USC4 composition; those have their own review obligations.

I made no change to an author source, Git object or ref. The only file written
by this reviewer is this review note.

## Exact source and imported-interface audit

Primary new sources examined:

* [hyper4_targets.md](../manuscripts/hyper4_targets.md), all sections;
* [hyper4_axis.md](../manuscripts/hyper4_axis.md), Section 2 and its stated
  pool, scale and global reservation interface;
* [hyper4_targets_controls.py](../../originals/code/hyper4_targets_controls.py), producer,
  independent verifier, arithmetic controls and corruption checks.

I byte-compared those files and the three persisted target inputs with
`git show` at the reviewed revision before running them. Relevant SHA-256
bindings are:

| File | SHA-256 |
|---|---|
| `manuscripts/hyper4_targets.md` | `d289b119e80b4fd93c9b277e26da96d32870675916c96aa6f03e54f881b64b1f` |
| `manuscripts/hyper4_axis.md` | `ca9cefea5142343144dfa27904279066743d67e7f79a4c763ff0fc3ab45e4496` |
| `code/hyper4_targets_controls.py` | `0ac81c15d119bc400291bd92c64bb6a12e2708d9df486fad9cd708757bf39fa5` |

I read the actual PR77 finite-list source
`explicit_prime_targets.md` at c2118dfad1aeb660d66308dc6a94d6c959f5010c (historical reference; not supplied in this package),
including its finite proof, and refetched that exact file through GitHub.
Its Git blob is `e9ee67afb4ba70aba454576ed88834b42d11fcf5`; the local export
has that same blob and SHA-256
`0e6ff5f0c26c6a2a6e66d0ae2b1a2ef581f282662a8e772e827ba04fd72f45e1`.
Thus the review did not rely on a stale statement or silently import a newer
cutoff interface. I also read the inherited
[cube target contract and TC](../manuscripts/cube_targets.md) and
[cube-controller supply argument](../manuscripts/cube_controller.md),
checking the dimension-dependent substitutions afresh.

The primary analytic paper was opened directly, including its printed page 3:
Jesse Thorner and Asif Zaman, *Refinements to the prime number theorem for
arithmetic progressions*, [arXiv:2108.10878v2](https://arxiv.org/pdf/2108.10878v2),
21 September 2021, Theorem 1.1, Remark 1.2, equation (1.6), and Section 1.2.
The polylogarithmic-modulus short-interval consequence is printed there. It
uses the ineffective Siegel-bound step to handle a possible exceptional zero;
it does not assume that such a zero is absent. The new manuscripts retain
that ineffectivity and do not claim a numerical threshold.

## Target construction: checks and attempted failure modes

### Compatibility and weights

For the proposed target of a line, the ordinary set of absolute fixed
coordinates removes both the coordinate signs and repetitions within a varying
block. In each disjoint-block partition identity, the two summands with the
same parameter have exactly the same label set. This checks the axis margins,
pair-family margins, triple-family totals and complementary-pair traces directly.
It is not an assumption that independently chosen prime matrices can have
compatible margins. No section sum is asserted prime.

I independently recomputed the weights of the axis three-tensor. They are
`1,8,18,48,24,48` for the six set types in the manuscript, and their total
is `1+26m+72 binom(m,2)+48 binom(m,3)=(2m+1)^3`. In particular the
`{0,a}` weight is 18, not 12 or 24. The finishing reserves therefore have
weights 8 and 18 exactly as used in HW.

The bulk greedy step has discrepancy at most `48d` independently of its
growing number of variables: each increment has sign opposite to the current
discrepancy and magnitude at most `48d`. The same two bracket primes may be
repeated as targets; no prescribed entry is reused by this step.

### Exact total, divisibility and parity

The center condition `q_0 = T-26m mod 4` is a unit class, since `T` is odd.
It makes `R=T-B-q_0` satisfy `R=26m mod 4`, using the fact that every bulk
weight is divisible by 8. Hence `R/2` has parity `m`.

Choosing `S_18 = R/2-4m mod 8` nearest to `m*mu` gives distance at most 4.
Then `S_8=(R/2-9S_18)/4` is integral, because its numerator is `4m mod 8`;
both finishing totals have parity `m`, and `8S_8+18S_18=R` exactly. The
displayed displacement `49d/8+9` for `S_8-m*mu` follows by direct expansion.
Dividing by `m` gives the required centers within `d/4` of `mu` under the
stated eventual hypotheses. No coefficient of order `m` or uncharged error
is hidden in this completion.

As an adversarial check, an arbitrary odd center would fail this scheme:
for `m=1`, `T=101`, `B=0`, and `q_0=5`, the residual is 96, whereas two
odd finishing totals have weighted sum `8+18=2 mod 4`. The actual mod-4
center condition excludes this failure. The bounded mod-8 repair is therefore
substantive and correctly retained.

### Every FL hypothesis at the two actual centers

Both applications use the original modulus **2**, unit residue 1 in every
coordinate, and length **`m=(n-1)/2`**, not length `n`. Their totals are
the integers `S_8,S_18` with the just-verified parity. The lemma permits
nonunit totals modulo other primes, so no unproved prime bracket in a
nonunit class is being requested.

For `ell_i=ceil(log_2 y_i)`, the source checks
`ell_i<=ceil(log_2 mu)+1`, so its hypothesis
`m>=60000(ceil(log_2 mu)+1)^11` implies the actual FL threshold
`m>=54000ell_i^11`. The radius satisfies
`2^20ell_i^11<=d<=y_i/4` eventually. Every FL interval lies within
`[mu-2d,mu+2d]`, and every auxiliary modulus up to `128ell_i^2` lies in
the uniform counting range. The strong original-modulus density and the weak
auxiliary-modulus density follow with their printed constants from TC, since
`2phi(q)log(2mu)<=4qell_i<=4qell_i^9` eventually.

Thus all four FL hypotheses, including the polynomial-logarithmic list length
and the entire auxiliary modulus range, are paid. There is no use of the
superseded ternary interface or of a theorem on a growing collection of
simultaneous prime affine forms.

## Analytic uniformity and four-dimensional supply

For targets, `beta=71/120`, `epsilon=1/240`, and fixed modulus exponent
`A=3` leave the exact positive slack
`beta-7/12-epsilon=1/240`. The minimum requested interval length is
`mu^beta/2000`, and the allowed moduli are eventually bounded by
`(log x)^3` for endpoints `x~mu`. This meets the printed short-interval
hypothesis uniformly. Dividing the weighted lower count by `log(2mu)` gives
TC. Endpoint conventions have no effect after enlarging the eventual threshold,
because the minimum main term tends to infinity with a spare constant margin.

At the actual pool scale, `X~4n^4log n`, `T~2n^8log n`, and
`mu~2n^5log n`. Hence the FL list-length ratio tends to infinity on the
entire odd tail, and `mu^(3/5)/X` tends to zero. Every resulting prime target
eventually exceeds every allowed gap `g<=16ceil(log_2X)`, so it is a unit
modulo all such gaps simultaneously. This does not require prescribing a
physical residue tensor during the analytic construction.

For pool supply, the narrow intervals have length proportional to `delta X`,
with logarithmic exponent ratio tending to `19/20` relative to `X`. This
strictly exceeds `7/12`, while `g=O(log X)`. Their counts are uniformly
`>>delta X/(g log X)`. In the worst allowed class this is
`>>n^(19/5)/log n`. The full reserve allowance is
`Q_*=2^40n^3K_4=O(n^(94/25))`; its ratio to that supply is
`O(n^(-1/25)log n)`, which tends to zero. This handles deletion concentrated
entirely in one requested window and one requested class, not merely average
depletion.

The common-gap seed selection uses disjoint consecutive pairs, then two
pigeonhole steps. Its supply is `>>X/log^3X` pairs in one reduced lower class.
The total old-plus-new seed demand remains `O(n^3P)=O(n^3log^2X)`, whose
ratio to the supply is `O(log^4n/n)`. Selecting seeds first is consistent
with the subsequent global deletion accounting.

I checked the finite grouped growth argument with its new constant rather
than importing the old pair count. Binning gives `s>=R/(2gF)` points. The
large differences have at least `s^2/4` edges spread over at most `R/g`
values. Thus some difference has at least `R/(16gF^2)>=256` edges when
`R>=4096gF^2`. The fixed-difference graph has degree at most two, so a greedy
matching has at least 86 edges, more than the forty requested. All differences
are in `[R/(32F),R]` and divisible by `g`. This is an actual disjoint matching,
not an assumption of a prime constellation.

For macro stages, the fresh lower and upper sets lie in disjoint intervals;
pigeonholing their difference yields
`>>delta^2X/(g log^2X)` pairs of one actual difference. For a fixed difference
these pairs already form a matching. This multiplicity tends to infinity
uniformly in `g`, so forty are available. The gap is in `[X/4,X/2]`, and
each midpoint differs from the exact pool mean by at most `delta X`.
Using reduced classes `-1,+1` gives the residue difference `2 mod g` for
every even `g`; primes in nonunit classes are never requested. Every selected
endpoint lies inside the prescribed pool interval.

The prefix complete-grid argument and the `32K_j` macro stages consequently
give the stated two-sided scalar capacity. This analytic review checks those
numeric resources; their realization at disjoint cells is left to the separate
geometry review.

## Replayed finite evidence

Environment: Python 3.12.14. Run from the repository root; each relevant
source and input was byte-equal to the reviewed commit before execution:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py self-test
python3 -B problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py check problems/prime-arrays-beyond-square/inputs/hyper4_targets_n3.json --negative-controls
python3 -B problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py check problems/prime-arrays-beyond-square/inputs/hyper4_targets_n5.json --negative-controls
python3 -B problems/prime-arrays-beyond-square/code/hyper4_targets_controls.py check problems/prime-arrays-beyond-square/inputs/hyper4_targets_n17.json
```

All four commands passed. The self-test exhausts the stated finite weight and
finishing-arithmetic fixtures. Persisted target checks returned:

| Order | Pool size | Exact pool total | Prime variables | Full lines | Partition identities |
|---:|---:|---:|---:|---:|---:|
| 3 | 81 | 15,535 | 3 | 272 | 154 |
| 5 | 625 | 1,340,727 | 7 | 888 | 298 |
| 17 | 83,521 | 42,747,841,521 | 129 | 23,400 | 2,170 |

Each of the order-three and order-five runs rejected all seven recorded
corruptions: changed total, omitted line, duplicate line, composite target,
invalid recorded residue, corrupted pair marginal, and an offset line posing
as a full line. The checker independently regenerates the initial pool and
the full line sets, using trial division rather than trusting the producer's
sieve. Its exact rational-power comparison correctly checks the target window.

These are target-vector certificates only. They do not establish actual
hypercube arrangements, FL's asymptotic hypotheses at these small orders,
or the eventual saturation theorem. The order-three and order-five outputs
explicitly decline an integer-image claim; the order-seventeen output cites
SI4 for it. The acceptance above rests on the conventional analytic argument
and the pinned imports, with these computations serving as regression checks.

After writing this note, `python3 -B check.py` also passed repository integrity
and all 45 tooling tests in the shared successor workspace. That separate
metadata/tooling result is not mathematical verification and is not a remote
CI result. A final byte comparison confirmed that the three reviewed source
files above still matched the frozen scientific revision.
