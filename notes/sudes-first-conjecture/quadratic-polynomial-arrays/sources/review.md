# Independent review of the improved polynomial bounds

Reviewer: an independent internal mathematical reviewer.
Author and reviewer were distinct research agents.
Exact scientific revision: **e0cf4e8808f21c0633326f70f42a870086836320**.
Verdict: **accepted in the scope stated below**.

This is an independent conventional mathematical and implementation review.
The reviewer did not design or contribute to the new polynomial argument.
It is not kernel verification, external referee acceptance, or construction
of an array at the stated large cutoffs. No correction to the frozen source
was required. The final source includes the author's pre-freeze clarification
that the same-degree binary difference restriction in Section 8 is for degree
at least two.

## Exact sources and imported contracts

The reviewed files, relative to `problems/prime-array-consolidation/`, are:

| File | SHA-256 |
|---|---|
| `manuscripts/polynomial_bound_transfer.md` | `269829f323333396a8b6abd9db422bf142f7d3c869a0789c1eba2d0f94d5d739` |
| `code/polynomial_bound_transfer.py` | `a055792d25dc13567b15aa14eaab454b66eef100b22199c70f74cacbdc647e3c` |

The original independent oracle reads these exact Git objects and checks both
digests before executing the candidate controls. The public adapter reads
the bundled byte-exact originals instead, with the same digest checks. The inspected working copies
had the same digests.

I read the actual canonical model, characteristic-zero proof, permutation
bridge, finite-field proof, and relevant original reviews from PR84. The main
scientific revision is
`3ea1a0389c2165a71d5abedf6b4c036f8b9f0166`; the auxiliary audit is
`158baa7c6122abde0b0aee42abb502477c04088f`; the reviewed delivery is
`3a4c5ade1b8762f3a0d982a1a448215a930179fc`.
The imported file digests in the new manuscript match the recovered text.

The canonical inputs remain the first `n^D` primitive irreducible positive-leading
integer quadratics in height and `(c,b,a)` order. No rescaling, shell completion,
or selected subpool is made. The required constraint family consists of all
`((n+2)^D-n^D)/2` full signed-coordinate lines for `n>=2`.

The argument imports the source's elementary reducible-height bound and
sampling-without-replacement concentration. I checked their required domains
and the composition. The negative-dependency theorem for canonical random
injection events remains the cited Lu--Szekely input in the already reviewed
permutation bridge. I rechecked the bridge's conflict budget and local-lemma
application; this review does not claim a new proof of that external theorem.

## Canonical density and conditioned sampling

The union bound over common prime divisors uses `sum p^-3`, `sum p^-2`, and
the harmonic tail with their stated elementary bounds. The final shell loss
is at most `12H^2`, independently of which lexicographic part is present.
Deleting all reducibles and the whole possible last shell is conservative.
At `H>=2^15`, the resulting error divided by `H^3` is below `3/4`;
`V_H>=4H^3` then gives density at least `13/16`.

At most `2n+1` deletions cost less than `1/80` of the box because
`V_H>=n^D>=n^2` and `n>=256`. Thus every residual population used in the
paired-sampling construction has density at least `4/5`, including the
population after excluding an arbitrary specified input. This uniformity
is necessary for the conditional bad-subset probability in PL and is present.

The lower leading mean follows from sorting the leading coordinates with
capacity `(2H+1)^2` per value. The lower-coordinate means use sign reflection
of the complete primitive box, followed by the actual reducible/shell/one-entry
loss. The bound `17+13 log(2H)` is sufficient. Height is established without
circularity: first use `N<=9H^3`, then the density estimate yields the sharper
`n^(D/3)/2<=H<=n^(D/3)` in the controller's range.

## Fourier estimate, concentration and the reducible window

PQ3's one-dimensional argument is valid for all `L>=5`. The overlap count
`|F intersection (F+v)|>=L/4` for `|v|<=floor(L/4)` gives the displayed
Dirichlet-kernel estimate. The two cases at `1/(2h+1)`, the sine lower bound,
and the quadratic cosine bound give the claimed `1/250` gap. The fraction
of entries in good coordinate fibers is at least `1/4`, even if the bad
fibers are arranged adversarially. Triangle inequality over the fibers
therefore gives `1/1000` for the actual dense three-dimensional population.
No uniformity or independence of coefficient coordinates is assumed.

For a distinct uniform pair, the exact without-replacement pair identity
only improves the upper bound by `|phi_E|^2`; Cauchy--Schwarz then gives the
`1/4000` exponent. Sequential conditioning pays every previously exposed
pair. A fixed included input contributes a unit-modulus phase. The one- and
three-dimensional Fourier inversions use the proper dimensions; in particular
the maximum-norm integral is `6 sqrt(pi) a^(-3/2)`. The constants `113` and
`2,800,000`, and the exponential tail `exp(-n/4096)`, all follow with the
stated rational margins. The finite-modulus consequence in Section 6 follows
from the same bound at nontrivial characters.

Separating `C=0` is legitimate and essential to the improvement. It is a
one-dimensional event and consumes the one-dimensional local mass bound.
For `C!=0`, PQ4 chooses a primitive linear factor with leading coefficient
`u<=sqrt(M)` and nonzero constant numerator. The factor may be chosen this
small even for nonprimitive output quadratics by putting the content in the
other factor. A root bound leaves at most `2Ru` numerators, with no additive
constant because zero is excluded. The leading window has length `s`, whereas
the lower-coordinate windows have length `2s`; the factors `s/u+1` and
`2s/u+1` are correct. Summing gives the claimed bound including repeated roots
and nonprimitive sums.

The actual-mean and leading-window inequalities give `A>=nH/4`,
`s<=nH/4`, and `s>=sqrt(M)`. The root estimate is bounded both by 2 and by
`7(T/n)^(1/4)`. They are used for different parts of the error, as required.
The estimates are uniform in the specified included input, including an
input from the unfinished top shell.

## Local-lemma budget and whole tails

The imported bridge uses canonical assignments, not an independence claim
for bad line sums. I checked both contributions to a canonical event's
neighbor probability sum: shared cells cost at most `n Delta b`, and shared
input entries cost at most `n Delta beta`. This yields the sufficient
`8n Delta beta<=1`, with `Delta<=r_D`. The pool and event space are finite
and `(N)_n>2` in every reported range.

The four contributions to `8n r_D beta` are correctly bounded. Their
budgets are respectively `<1/16`, `<=1/64`, `<=7/8`, and `<=1/64`.
Their total is strictly below `31/32`. In particular the zero-constant
coefficient is `1808`, the nonzero-root coefficient is `896 C_3`, and the
exponential remainder contains both local-mass remainders. The coarse
logarithmic error condition expands to exactly the last line of PQ-C.

All positive-power transformations in PQ-C preserve inequality direction.
The factor `1024=(8/7)896` is correct. The integer comparisons thus certify
the probability budgets rather than a numerically fitted approximation.
The mean and nonzero-root ratios have negative logarithmic derivatives
for all real `y>=10,D>=2`; the other ratios have the stated monotonicity.
The tests therefore cover every intervening integer order and partial shell,
not only powers of two. The closed bound PQ-U is also proved uniformly in
dimension: its exponentially small factors dominate the increases in `r_D`,
`T`, `U`, and `A_0`, while `D<2^(y/2-12)` pays the remaining linear conditions.

I accept PQ1, the displayed least exponents **of this sufficient controller**,
and the closed bound PQ-U. In particular the canonical quadratic square
conclusion improves from `n>=2^3072` to `n>=2^120`, with both order parities.
The analogous cube exponent is 67. These are irreducibility-over-`Q`
conclusions. The explicit lower bound on nonprimitive-sum probability
correctly prevents relabeling them as primitive-`Z[x]` conclusions.
The effective construction mentioned is exhaustive enumeration; no practical
running time is inferred from the local lemma.

## Independent implementation checks and recovery

The separate reviewer oracle is
[`polynomial_transfer_independent_oracle.py`](../code/polynomial_transfer_independent_oracle.py), SHA-256
`3f48ef9f0f7981b9854c0a6dd3e54f55185a7ca85ef19b9b86a0fb1cbb88702d`.
Its deterministic JSON stdout has SHA-256
`6749fe80de7a90d39c98aecefc513e5b900ce0a107ac62473996a441bc96e949`.
The original output was transient; the public replay regenerates it exactly. The durable evidence consists of this review,
the source-bound oracle, and the mathematical proof.

The independent checks passed:

* Primitive linear-factor enumeration and discriminant enumeration produced
  identical reducible sets in three windows: 106, 457, and 1893 reducibles
  among 214,872 quadratics. This checks the window orientation and the
  nonzero-constant separation with a different enumeration method.
* Frobenius/gcd irreducibility, rather than the producer's trial divisors,
  reproduced every binary shell through degree 12. Independent Mobius
  inversion agreed with the producer's divisor recurrence and with 188
  resource invoices, including all displayed finite endpoints.
* Direct enumeration of 57,768 full signed lines in eight small geometries
  found exactly the prescribed exceptional axes and the correct crossing
  counts. A too-small `n=5,D=4` geometry has an additional signed line,
  confirming that the geometry restriction is substantive.
* Independent pre-controller budget evaluations and linear scanning made
  710 exact comparisons in dimensions 2 through 30, 50, 100, and 1000.
  They reproduced every displayed exponent and the rejecting predecessors.
* Exhaustive conditional binary samples gave 0 successes among 28 sets at
  order 3 and 213 among 10,626 sets at order 5, respecting PF2. Success
  was tested by the independent Frobenius/gcd predicate.

The author's complete deterministic `test` command also passed. These
controls support the proof audit; sampled later exponents do not replace
the analytical whole-tail argument reviewed above.

Reproduce from the public bundle using the commands in [the code guide](../code/README.md). The public adaptation changes only the source-loading path: it reads the included immutable originals and verifies their original digests instead of invoking Git against the private research history. The separate original reviewer script is retained for provenance. The complete regression includes historical binary-subsystem checks; these are not assertions of complete finite-field arrays.
