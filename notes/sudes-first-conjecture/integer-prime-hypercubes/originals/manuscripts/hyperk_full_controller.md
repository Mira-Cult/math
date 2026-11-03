# A uniform sparse real frame for the full signed-line kernel

Author: `/root/controller`. This is a new component of the continuation after
delivery `1e7883d705cafbaf717bfacefcf6695baebf6dbe`; the delivered manuscripts
remain unchanged. Labels are local. The author is excluded from independent
review of this component.

This source proves a target-independent sparse frame and its rounding
interface. The exact integer absorber and the assembly into prime
permutations are separate components. In particular a real frame, or an
integer array in a kernel, is not itself a prime-array certificate.

## 1. Statement and dependencies

Let `I={-m,...,m}`, `n=2m+1`, and let `K_d` be the common integer kernel
of every full signed-coordinate line contraction on `I^d`. Its real span
is denoted `K_d(R)`. The center is retained as one label. A **unit template**
is an array with entries in `{-1,0,1}` belonging to `K_d`. Its zero axis
sums allow its positive and negative cells to be paired along each chosen
coordinate. Such a template is suitable for fresh equal-gap prime pairs,
but availability of those pairs and placement in the higher-dimensional
array are separate obligations.

**Theorem UF(d,eta).** Fix `d>=1` and `eta>0`. For every sufficiently large
odd `n`, there is a finite, fixed collection `J=(J_alpha)` of unit templates
on `I^d`, chosen independently of the tensor to be corrected, with:

1. `|J| <= C_(d,eta) n^d log n`;
2. every support has at most `q_d` cells, where `q_d` depends only on `d`;
3. every cell belongs to at most `C_(d,eta) log n` supports, counting
   multiplicities and dormant templates;
4. for every `D in K_d(R)` there are real coefficients with

   `D=sum_alpha c_alpha J_alpha`,
   `max_alpha |c_alpha| <= C_(d,eta) n^eta ||D||_infinity`.

For integer `D in K_d`, rounding these coefficients to nearest integers
leaves an integer tensor `R in K_d` satisfying

`||R||_infinity <= C_(d,eta) log n`.                    (UF1)

Thus the real approximation has a logarithmic **integer kernel** remainder.
The collection is selected once and works for every `D`; the proof does
not choose reservoir geometry after observing an array's line errors.

The local inputs are the monic kernel basis KG in
[the incidence manuscript, Section 5.2](hyperk_incidence.md), and the pure
unit selectors PS in [the kernel supplement](hyperk_kernel_research.md).
Both are proved there for every fixed dimension. The only additional
external probability result is the rectangular matrix Bernstein inequality
in Joel A. Tropp, *User-Friendly Tail Bounds for Sums of Random Matrices*,
Theorem 1.6, arXiv:1004.4389v7, published in *Foundations of Computational
Mathematics* 12 (2012), 389--434. Primary source:
<https://tropp.caltech.edu/papers/Tro11-User-Friendly-preprint.pdf>.
All parameters required by that theorem are bounded explicitly below.

## 2. A random common-marker basis has bounded expected incoming support

Put

```
h=(3^d-1)/2,  D0=d^2(d+1),  s=2h+1=3^d,
S=s^d,  C=s^D0,
G=(2h+2)^(D0+1) sum_(j=0)^d (6h)^j.                   (UF2)
```

Choose an injection `a: H_d -> {1,...,m}` uniformly; its images are the
designated positive marker orbits in the monic construction. For a cell
`v`, let `K_v^a` be its KG basis vector if its cell monomial is standard
for this marker assignment, and zero otherwise. The fixed-marker identity
is, for every `M in K_d(R)`,

`M=sum_(v in I^d) M(v) K_v^a`.                         (UF3)

The local bounds hold uniformly in `a,v`:

`|supp K_v^a|<=S`, `||K_v^a||_infinity<=C`.

**Lemma ER.** For all sufficiently large odd `n` and every output cell `y`,

`sum_v P(K_v^a(y) != 0) <= G`.                         (UF4)

### Proof, including the center

Call a leading monomial **active** if it divides the current cell monomial
in monic reduction. Active leading blocks have disjoint coordinate sets:
two different blocks use different marker orbits, so they cannot both use
one coordinate of a multilinear monomial. There are at most `d` active
blocks.

One rewrite removes its selected active block. Any newly active block
must intersect the rewritten coordinates, so its designated orbit must
equal the absolute value of the new common parameter. There is at most
one such designated block. Hence a rewrite never increases the number of
active blocks. If the new parameter is outside all designated marker
orbits, it creates no active block and decreases their number by at least
one. This includes parameter zero: zero is never a designated marker.

If `y` initially has `r` active blocks, a reduction branch therefore makes
at most `r` nonmarker choices. Every other choice is among at most `2h`
signed marker values. Each branch has at most `D0` rewrites by the weight
bound in the incidence proof. Counting all such branches gives at most

`(2h+2)^(D0+1) n^r`

standard monomials with nonzero coefficient in `NF(z_y)`. Cancellations
can only decrease that count. By the definition of KG, this is also an
upper bound for the number of `v` with `K_v^a(y)!=0`.

For any prescribed collection of `j` active blocks, its `j` distinct
designated orbits must match `j` specified nonzero absolute labels of `y`.
The probability is either zero or `1/(m)_j`, where the denominator is a
falling factorial. There are at most `h^j` ordered candidate collections.
For `m>=2d` we have `n^j/(m)_j<=6^j`. Consequently

```
E n^r <= sum_(j=0)^d n^j P(r>=j)
       <= sum_(j=0)^d h^j n^j/(m)_j
       <= sum_(j=0)^d (6h)^j.
```

This proves (UF4). In particular the support inclusion in KG is not
being treated as if every coordinate could become an arbitrary marker
independently. The active-block count is the additional fact that removes
the otherwise false growing incoming-load estimate. QED.

## 3. Turning every compact integer kernel column into unit templates

Let `Z in K_d` have at most `S` support cells and coefficients of magnitude
at most `C`. Its coordinate orbit set has at most `dS` elements. Choose
distinct positive anchors `b_1,...,b_d` outside that entire orbit set.
For each signed block `H=(B,sigma)` with `|B|>=2`, choose a reflected pure
selector `Q_H`. Its whole positive orbit alphabet is disjoint from every
other selector alphabet, the anchors, and the entire support of `Z`.
Selectors indexed by `H` are reused consistently within this one column.

For `x in supp Z` put

`R_x=tensor_i(e_(x_i)-e_(b_i))`.

Zero axis sums imply the exact integer identity

`Z=sum_x Z(x) R_x`.                                    (UF5)

For a nonaxis signed block `H`, the contraction scalar `beta_H(R_x)` is
either zero or one. Indeed a common parameter cannot use an anchor:
anchor orbits are distinct and avoid every coordinate orbit of `x`.
Thus its only possible witness uses the original endpoint `x_i` in every
coordinate of the block, each with coefficient `+1`. This remains valid
when that witness is zero or when original coordinates are reflected.

For a collection `pi` of disjoint nonaxis signed blocks define

```
P(R_x)=sum_pi (-1)^|pi|
  (tensor_(H in pi) beta_H(R_x) Q_H)
  tensor (tensor_(i outside union(pi)) (e_(x_i)-e_(b_i))). (UF6)
```

**Lemma PU.** Each `P(R_x)` is a unit template. Moreover

`Z=sum_x Z(x) P(R_x)`                                  (UF7)

exactly, with at most `S` unit templates and coefficients bounded by `C`.

**Proof.** The pure-selector cancellation in LP of the kernel supplement
shows that (UF6) has every signed-line contraction zero. Each tested block
either pairs the terms `pi` and `pi union {H}`, is properly inside one
pure selector, or crosses disjoint orbit alphabets. These respectively
cancel, vanish by purity, and miss the support. Axes vanish term by term.

Different nonzero partition terms have disjoint supports: some coordinate
belongs to different alphabet groups in any two different terms. Every
coefficient within a term is `+1` or `-1`, since all nonzero `beta_H` equal
one. Thus the whole tensor has only unit signed entries.

The formula defines one linear operator on arrays supported on the
alphabet of `Z` and the anchors:

`P(W)=sum_pi (-1)^|pi| Q_pi tensor C_pi W`,

where `C_pi` is the corresponding repeated contraction. The required
alphabet separation holds for every `R_x` simultaneously. Since every
nonempty contraction of `Z` is zero, `P(Z)=Z`. Apply this to (UF5) to obtain
(UF7). This common-operator identity is why independent pointwise projector
choices would not have been enough. QED.

For finite constants, let `a_b,s_b` be the positive-alphabet and support
recurrences of PS in the kernel supplement, and let `Pi_d` denote all
collections of disjoint signed blocks of size at least two. Define

```
A_d=d+sum_(b=2)^d binom(d,b) 2^(b-1) a_b,
q_d=sum_(pi in Pi_d) 2^(d-|union pi|) product_(H in pi) s_|H|,
F_d=sum_(pi in Pi_d) 6^|pi| 7^(d-|union pi|)
                                  product_(H in pi) s_|H|.       (UF8)
```

Empty products equal one. Each unit template in (UF6) has at most `q_d`
cells. The construction uses at most `A_d` new noncentral orbits. These
are finite recurrences in `d`, not estimates inferred from fixed examples.

## 4. Unit physicalization preserves expected incoming support

For each sampled KG column choose the whole ordered auxiliary alphabet
in Section 3 uniformly without replacement from positive orbits outside
that column's entire support. Choices for different sampled columns are
independent. The finite number of excluded orbits is at most `dS`.

**Lemma EP.** The expected number of unit templates containing any fixed
cell `y`, summed over one independent KG sample for each input cell `v`,
is at most `G F_d`, for sufficiently large `n`.

**Proof.** Consider one partition term `pi` in (UF6), a support word in
each of its pure selectors, and a subset `J` of uncovered coordinates
where the anchor endpoint is used. If the term is nonzero, the input
cell `x` is signed-constant on each block of `pi`; uncovered coordinates
outside `J` must equal the specified coordinates of `y`. There are at
most

`n^s`, where `s=|pi|+|J|`,

possible such input cells: one parameter for each block and one for each
anchor coordinate. To hit `y`, the independently selected auxiliary
alphabet must realize at least `s` prescribed distinct orbit labels:
one from each selector block and the `|J|` separate anchors. If any
required labels conflict, the probability is zero. Otherwise it is at
most `6^s/n^s` once the ambient order exceeds the fixed exclusions. The
bound is uniform in the sampled column and its excluded support.

Sum first over input cells `x`. Lemma ER bounds the expected number of
KG columns containing each such `x` by `G`. The factors `n^s` and
`n^-s` cancel. Summing over `J` gives `7^(d-|union pi|)`; summing selector
support words and then `pi` gives exactly the upper bound `G F_d`.
This counts support incidences, not net coefficients or zero traces.
QED.

## 5. Sampling one universal operator

Write `N=n^d`. For every input cell `v` and every `j=1,...,T`, sample an
independent marker assignment `a(v,j)` as in Section 2. Define

`A=(1/T) sum_(v,j) K_v^(a(v,j)) e_v^*`.                 (UF9)

The expectation `Abar` is the average of the common-marker projections
in (UF3). Therefore

`Abar|K_d(R)=identity`, and `A(R^N) subset K_d(R)`.      (UF10)

This equality holds for every tensor in the kernel, not merely for an
independent random target. We seek one sample with a small spectral
deviation and bounded row load.

For the centered summand

`X_(v,j)=(K_v^(a(v,j))-E K_v^a)e_v^*/T`

we have

`||X_(v,j)||_2 <= 2 C sqrt(S)/T`.

For one variance sum, the matrices `E X*X` are diagonal in `v`, so

`||sum E X*X||_2 <= SC^2/T`.

For the other, discard the nonnegative covariance subtraction in the
positive-semidefinite order. Its absolute row sum at `y` is at most

```
(1/T) sum_v E( |K_v^a(y)| ||K_v^a||_1 )
    <= SC^2 G/T.
```

Hence the rectangular Bernstein variance parameter is at most `V/T`,
where `V=SC^2 max(1,G)`. The theorem stated in Section 1 gives

```
P(||A-Abar||_2 > epsilon)
 <= 2N exp( -T epsilon^2 /
                 (2V+(4/3) C sqrt(S) epsilon) ).        (UF11)
```

Independently of any input tensor, the number of sampled KG columns
containing a fixed cell has mean at most `TG`, with independent indicators.
Scalar Bernstein and a union bound imply that, with failure probability
at most `N exp(-T)`, every such count is at most `(2G+2)T` after enlarging
the harmless constant in `T`. Thus

`||A||_(infinity->infinity) <= C(2G+2)`.                (UF12)

Physicalize each sampled column independently as in Section 3. For one
column the number of resulting templates through a fixed point is at
most `S`; by EP its total mean over columns is at most `TGF_d`. The
bounded-variable scalar Bernstein inequality gives, again simultaneously
over all output cells,

`pointdegree <= rho_d T`,  `rho_d=2GF_d+2S`,             (UF13)

with failure probability at most `N exp(-T)` after the same enlargement.
For example, for variables bounded by `S`, the variance is at most `S`
times their total mean; taking excess `T(GF_d+2S)` in the scalar Bernstein
formula gives an exponent at least `T`.

Consequently for every `0<epsilon<=1/4` there is a finite constant `M_d`
such that

`T=ceil(M_d epsilon^-2 log(16N))`                       (UF14)

makes all three failures total less than one. All inequalities above give
an explicit choice: taking `M_d` larger than

`64( V+C sqrt(S)+S+G+GF_d+1 )`

suffices. Fix one successful sample, including all its physicalizations.
This sample is fixed before a target or initial prime arrangement is
chosen. Its collection contains at most `NST` unit templates and obeys
(UF13).

## 6. A small spectral error gives an arbitrarily small power loss

Put

`L=1+C(2G+2)`,  `epsilon=min(1/4,L^(-(d/eta+2)))`.

On `K_d(R)` set `R0=identity-A`. By (UF10)--(UF12),

`||R0||_2<=epsilon`, `||R0||_infinity<=L`.

For `D in K_d(R)`, the Neumann series

`z=sum_(j>=0) R0^j D`                                 (UF15)

converges and satisfies `Az=D`. There is no integer division in this
step; it is explicitly a real coefficient construction. Its terms obey

`||R0^j D||_infinity <= min(L^j, n^(d/2) epsilon^j) E`,

where `E=||D||_infinity`. Split the geometric sum at

`j*= (d log n)/(2 log(L/epsilon))`.

Both parts are at most a constant times

`n^theta E`,  `theta=d log L/(2 log(L/epsilon)) < eta`.

Thus `||z||_infinity<=C_(d,eta)n^eta E`. This interpolation between the
two norms is essential: a one-step uniform contraction in the supremum
norm is neither asserted nor needed.

For each sampled column, use the exact expansion (UF7). The coefficient
of its unit template indexed by `x` is

`c_(v,j,x)=z(v) K_v^(a(v,j))(x)/T`.

Their sum is `Az=D`, and their magnitudes are at most
`C C_(d,eta)n^eta E/T`. The coarser bound in UF follows. Every template
has bounded support and is pairable along every coordinate, as already
proved. This completes the real-frame statement.

For integer `D`, round each real coefficient to a nearest integer.
Each template is integral and in the full kernel, so the remainder is
integral and in the full kernel. At a cell, each of the at most `rho_d T`
templates contributes rounding error at most `1/2` in absolute value.
Therefore `||R||_infinity<=rho_d T/2`, proving (UF1).

One may equivalently round the single scalar `z(v)/T` of each sampled KG
column before its physicalization. The integer coefficients in (UF7)
then keep the physical coefficients integral. Its remainder bound is
`C(2G+2)T/2`, also logarithmic. The companion exact matrix fixture replays
this version, avoiding any inference from floating-point inversion.

## 7. Interface to the exact integer absorber and the physical ledger

Suppose a fixed integral unit-template frame `I_d` has bounded point
degree and represents every `W in K_d` with coefficients bounded by

`C_d n^d ||W||_infinity`.                              (UF16)

The separate stratum/chessboard construction is responsible for proving
(UF16). Applying it only to the remainder in (UF1) gives a combined
fixed frame with numerical coefficient bound

`C_(d,eta)( n^eta ||D||_infinity + n^d log n )`.         (UF17)

If actual discrepancies are in units of an even common prime gap `g`,
the physical coefficient bound is

`C_(d,eta)( n^eta E + g n^d log n )`.                   (UF18)

For a native signed block of size at least two in ambient dimension `k`,
its complement has `d<=k-2`. Hence the second term is `o(X)` for
`X~k n^k log n` and `g=O(log X)`. The first term is affordable by choosing
`eta` below the slack between successive capacity exponents in the
finite-in-`k` resource ladder. The logarithmic point degree and template
count multiply reservation and line-load estimates by logarithmic factors;
they do not alter the number of algebraic correction levels.

These observations specify the quantitative interface. They do not replace
the direct proof of the signed-partition correction hierarchy, residue
repair, equal-gap supply, fresh placement, or centered initial completion.
Those components must use the entire template collection, including
zero-coefficient templates, when bounding occupancy.

## 8. Reproducible controls and limitations

Run from the repository root with Python 3.11 or later:

```sh
python3 -B problems/prime-arrays-beyond-square/code/hyperk_full_controller.py
```

The companion `code/hyperk_full_controller.py` tests monic normal forms,
the active-block monotonicity used in ER, exact local physicalization,
full signed-line signatures, center and reflected witnesses, and small
finite samples of the uniform operator. Its spectral upper bounds use
exact rational row and column norms, and its inversions use fraction-free
integer elimination followed by rational substitution. These finite
computations are diagnostics, not a proof of the large-order matrix bound. They do
not construct a complete prime arrangement and do not establish the
separate integer absorber (UF16).

The author run passed the following controls:

| Control | Exact result |
|---|---|
| All common-marker injections at `d=1,2`, `n=9` | 4 and 24 exact reconstruction identities |
| Independent-column sampled operators | Squared spectral norm of `A-Abar` is at most `8967/2097152` and `19022491/301989888`, respectively |
| Rational inversion and integer rounding | Exact real reconstruction; integer full-kernel remainders have norms 920 and 5261, below their respective point-load bounds `5663/2` and 156285 |
| Compact KG physicalization at `d=1,2,3` | 12 columns, including center, reflection, and coefficient magnitudes two and three, reconstruct exactly using 185 unit templates |
| Pairing and actual partial prime switches | 510 coordinate-fiber pairings and 12 fresh-pair switch fixtures, with independent trial primality and unchanged partial pools |
| Active leading-block count | 42,720 further rewrite checks at `d=4,5,6`, including 840 strict nonmarker decreases |
| Malformed inputs and false shortcuts | Six rejected controls, including reused/central marker labels, a nonkernel input, incoherent local projector alphabets, and a wrong switch sign |

The number of samples per input cell in the two finite operator fixtures
is 2048 and 8192. These deliberately generous finite values are not
asymptotic threshold estimates. The dimension-five and dimension-six
symbolic unit-template support bounds from (UF8) are 172,064 and 8,013,504;
their size affects constants only, since dimension is fixed first.

The failed alternatives relevant here are explicit. Independent local
kernel projection does not preserve exact global reconstruction. A fixed
marker basis can have unbounded point load. Pointwise concentration for a
fixed target does not make a universal controller. Rounding outside a
unit full-kernel frame need not leave a compatible integer residual.
The proof above supplies, respectively, an unbiased common-frame identity,
an expected incoming-support count, a uniform spectral estimate, and
rounding inside the kernel.
