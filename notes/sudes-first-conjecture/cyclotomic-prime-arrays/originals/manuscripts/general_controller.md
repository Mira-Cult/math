# Physical prime-array control in every fixed arithmetic rank

Author: `/root/controller`. All result labels are manuscript-local. This is an
additive continuation of the quartic work. The frozen [quartic controller](controller.md)
and its finite checker are unchanged. This manuscript proves a fixed-rank
physical transfer theorem under explicit representative-geometry and prime-box
hypotheses; those hypotheses must be verified for any proposed new canonical
pool. It does not identify different unit normalizations.

The exact earlier scientific source is
`6f8524253c32db096e38715fd69e880e0fa85fdd`. Its DG lemma already has arbitrary
fixed-rank scope. Its IT theorem supplies the rank-independent integer tensor
correction used here. The remaining generalization, including every rank loss
and a complete sufficient parameter regime, is proved below. This draft's
independent review is to be recorded separately against its frozen revision.

## G1. The transfer statement and its hypotheses

Fix a number field `K` of degree `r>=2`, its integer ring `O`, and an ordered
integral basis identifying its additive group with `Z^r`. The field, basis,
and rank remain fixed while the side length tends to infinity. Array dimension
is `D=2` or `D=3`. All vector maximum norms below are in the integral basis;
the induced matrix infinity norm is the maximum absolute row sum.

Let `P` be a previously frozen ordered sequence of distinct prime elements,
one specified representative of each contributing prime-element associate
class. Let `A_M` be its exact first `M` elements. For `M=n^D`, put

\[
 B=\max_{a\in A_M}|N_{K/\mathbb Q}(a)|,
 \quad R=B^{1/r},\quad\ell=\log R,
 \quad T=\sum_{a\in A_M}a,
 \quad\bar a=T/M,\quad\mu=n\bar a.                       \tag{G1.1}
\]

In a field of class number greater than one, contributing classes mean
generators of **principal prime ideals**. Nonprincipal prime ideals and
nonprime irreducibles are not entries. All input choices, omitted classes,
and tie conventions belong to the frozen sequence, before this theorem is
applied.

Let

\[
 \mathfrak d_2=\prod_{N\mathfrak p=2}\mathfrak p,
\]

with the empty product equal to `O`. This is a fixed integral ideal. The
following are the transfer hypotheses.

**H1: density and boundedness.** The exact prefixes satisfy

\[
 M\asymp_K R^r/\log R,\qquad
 A_M\subset[-C_KR,C_KR]^r.                               \tag{G1.2}
\]

Consequently, for either fixed array dimension,

\[
 R\asymp_K n^{D/r}(\log n)^{1/r},\qquad
 \log R\asymp_K\log n.                                  \tag{G1.3}
\]

For a canonical pool containing one representative per principal prime ideal,
the intended sharper input is `M(B) ~ Li(B)/h_K`, where `h_K` is the class
number. Thus `B ~ h_K M log M`; the density constant is **not** silently
replaced by one when the class number exceeds one. The physical proof needs
only (G1.2), so this fixed factor changes no exponent. Higher residue degrees
and the last incomplete norm tie remain in `A_M` and in its exact total.

**H2: canonical interior chords.** There is a bounded real canonical domain
`Omega` in `K tensor R`, with positive norm strictly less than one at its
interior points, such that its prime elements are the chosen representatives
of their associate classes. A representative whose class contributes to the
frozen sequence belongs to the prefix whenever its norm is below `B`.
The only omitted classes relevant here are the frozen finite exclusions;
the endpoint neighborhoods below have normalized norm bounded away from zero,
so those finitely many canonical representatives cannot enter them for large
`R`. The means satisfy `bar a/R -> u`. There are `r` fixed
independent real vectors `v1,...,vr` for which all

\[
 u-v_j/2,\qquad u+v_j/2                                  \tag{G1.4}
\]

are strict interior points of `Omega`. Fixed neighborhoods of these endpoints
remain inside the domain and below a fixed norm fraction of the cutoff.
No convexity of `Omega`, and no assertion that `u` itself belongs to `Omega`,
is required. It is enough to prove that
`Omega intersect (2u-Omega)` has nonempty full-dimensional interior: the
available gap vectors then form an open subset of `R^r`, from which `r`
independent vectors can be selected once and for all. Their conditioning
is a fixed field/domain constant.

**H3: uniform prime boxes at those endpoints.** For every pair of fixed
positive exponents `a,b`, every coefficient box of radius a fixed positive
multiple of `eta R`, `eta=ell^-a`, lying in the fixed endpoint neighborhoods,
has, in every unit class modulo every ideal of the form

\[
 \mathfrak q=d\mathfrak d_2,\quad d\in\mathbb Z_{>0},
 \quad N\mathfrak q\le\ell^b,
\]

at least

\[
 c_{K,a,b}\frac{\eta^rR^r}{\varphi_K(\mathfrak q)\log R}
 \asymp_K c_{K,a,b}\frac{\eta^rM}{\varphi_K(\mathfrak q)}   \tag{G1.5}
\]

prime elements. The estimate is uniform over the indicated locations and
classes. The boxes may be translated from the limiting mean to the actual
mean. Their positive domain margin makes this valid eventually. This
hypothesis is an analytic statement about actual prime elements in the
canonical domain, not an ideal-counting statement without generators.
It is only required at logarithmically relative widths; an ineffective
threshold is permitted.

**H4: the norm-two input coset.** Every input lies in the class one modulo
each norm-two prime ideal, equivalently

\[
 a\equiv1\pmod{\mathfrak d_2}\qquad(a\in P).              \tag{G1.6}
\]

This is automatic if there are no norm-two primes. It is also automatic if
every contributing norm-two prime class is among the omissions already
specified in the frozen model. It is not silently imposed by discarding a
retained exceptional entry during the proof. Input elements can be nonunits
modulo other prime ideals dividing an adaptive modulus; they stay in the
pool and, if unused by a gadget, in the filler.

For a square, call a target vector compatible when both the row list and
the column list have exact total `T`; the two diagonal targets are free.
For a full signed cube, require all axis plane-marginal identities, axis
directional total `T`, and the six identities equating a slice-diagonal
family total with the corresponding diagonal sum of the perpendicular
axis-target tensor. These are the full integer compatibility equations for
sufficiently large `n` in the pinned geometry; the four body targets add
no further equation.

**Theorem GC(r) (proved physical transfer).** Under H1--H4, both array
dimensions have the following property for every sufficiently large integer
`n`. Every compatible target vector `tau` with entries in `O` such that

\[
 \tau_L\equiv n\pmod{\mathfrak d_2},\qquad
 \|\tau_L-\mu\|_\infty\le H=nR/\ell^{h_r}                 \tag{G1.7}
\]

is realized by one permutation of precisely `A_(n^D)`. Here a valid explicit
fixed exponent is given in Section G7. Every full signed-coordinate line is
included. The theorem does not require target values to be distinct or to
be canonical representatives.

The statement is a physical realization theorem, so it permits nonprime
targets and every large side length. A subsequent prime-target theorem
typically uses odd `n` when `d_2` is proper and every `n` when `d_2=O`.
Any necessity claim about those order restrictions, including the possible
exception of a prime sum that is an associate of a small prime, remains a
separate local-arithmetic obligation.

## G2. Spatial imports and the distinction between the two dimensions

The integer incidence and support geometry are the immutable sources already
audited in the quartic proof:

* ordinary source `a2445962ec6e06b2a893980fb7a183057eb9bcee`,
  `problems/prime-arrays-beyond-square/manuscripts/{signed_trades,signed_cube,
  cube_controller,incidence}.md`;
* square support source `c2118dfad1aeb660d66308dc6a94d6c959f5010c`,
  `problems/prime-line-sums/manuscripts/explicit_controller.md`, Section 3;
* quadratic source `e6e581efb9b676a7d5bc88b91c01571b087ed5da`,
  `problems/quadratic-prime-arrays/manuscripts/vector_controller.md`, Section 5,
  and its `local_arithmetic.md` for the even-order signed-cube extension.

These are assertions about positions and additive incidence vectors. They
hold with any abelian group as the entry payload. A stage uses the following
number of **actual disjoint equal-gap pairs**:

| Spatial operation | Pairs per stage | Signed change |
|---|---:|---|
| Ordinary transfer | 1 | one positive and one negative endpoint |
| Rectangle | 2 | `delta [[1,-1],[-1,1]]` |
| Cuboid | 4 | `delta (-1)^(i+j+k)` on eight vertices |

The gap `delta` is one element of `O`, with all `r` coordinates. Increasing
arithmetic rank does not turn a cuboid into an `r`-dimensional spatial
object. It increases the fixed number of arithmetic directions and the
conditioning losses, all paid below.

Use the imported loopless multigraphs of degree at most 64 and edge expansion
at least 8. Ordinary integral graph flows cost a fixed multiple of the
largest zero-total vertex demand. The graphs have `O(n)` edges. In cubes,
their products give `O(n^2)` rectangle types. The support contracts also give:

1. disjoint supports and per-line prefix/main/modular load bounds of the
   corresponding stage count, whenever that count is `o(n)`;
2. old numerical axis supports avoiding every body diagonal;
3. new face supports preserving every axis, every body, and all other face
   families;
4. body supports using fresh reflection orbits so that their entire action
   adds only `O(R)` drift to any one face line;
5. each nonnative required line meeting at most a fixed number of effective
   stages of one main reservoir, or being preserved exactly.

The even-order extension uses reflection orbits of size two and five
noncentral orbits; it is available for every `n>=10`. It has no arithmetic
rank dependence. Fixed-rank constants can multiply stage counts without
affecting the hypothesis `stage count=o(n)`.

## G3. Dense actual gaps, the seed lattice, and a contained ideal

The frozen DG lemma, [quartic controller Section 3](controller.md), is an
elementary statement in arbitrary fixed rank. Applied with

\[
 A\subset[-U,U]^r\cap\mathbb Z^r,\quad s=|A|\ge U^r/L,
 \quad C_r dL\le H\le U,
\]

it gives independent actual gaps `g1,...,gr` in `d Z^r` with

\[
 \|g_j\|_\infty\le H,\quad
 |\det G|\ge(H/(C_rL))^r,\quad
 \|G^{-1}\|_\infty\le C_rL^r/H,                           \tag{G3.1}
\]

and `gg_r s/L` mutually disjoint pairs in each of the `r` directions.
Its proof partitions into `H`-cubes and residue classes modulo `d`, then
excludes a thin neighborhood of the span of previously chosen gaps. The
thin-slab count is

\[
 (2H/d+1)^{r-1}(2\sqrt r\,h/d+1),
\]

while the pair count is at least `s H^r/(2*4^r d^r L)`. Taking
`h=H/(C'_r L)` gives the independence and conditioning bounds. A fixed-gap
pair graph has degree at most two, so deleting the earlier selected
matchings still permits mutually disjoint direction families. This lemma
counts actual endpoints, not merely lattice vectors.

Under H1, take `U=C R` and `L=C' ell`, with sufficiently large fixed
constants. Every deletion of `o(M)` entries still satisfies the density
hypothesis. Apply DG at seed scale `H_s=ceil(C_r L)` and `d=1`; write

\[
 G=[g_1\ \cdots\ g_r],\quad\Gamma=G\mathbb Z^r,
 \quad d_\Gamma=|\det G|,\quad\mathfrak q=d_\Gamma\mathfrak d_2.
                                                               \tag{G3.2}
\]

H4 puts all seed differences in `d_2`. The adjugate identity in the fixed
integral basis proves, without any ideal assumption on `Gamma`,

\[
 \mathfrak q\subseteq d_\Gamma O\subseteq\Gamma
               \subseteq\mathfrak d_2.                    \tag{G3.3}
\]

The exact additive index in `O` is `d_Gamma`. The estimates needed later are

\[
 \begin{split}
 d_\Gamma&=O_K(\ell^r),&\|G\|_\infty&=O_K(\ell),\\
 \|G^{-1}\|_\infty&=O_K(\ell^{r-1}/d_\Gamma),&
 \kappa_G&=O_K(\ell^r),\\
 N\mathfrak q&=N(\mathfrak d_2)d_\Gamma^r
                =O_K(\ell^{r^2})\le\ell^{r^2+2}
                \quad\text{eventually}.                  \tag{G3.4}
 \end{split}
\]

The inverse estimate here is the adjugate estimate, stronger at the seed
scale than the generic DG inverse bound. Each seed direction has a matching
of size `gg_K M/ell`. Reserve all seed copies needed for all future
reservoirs first. Section G7 checks their combined demand against that
matching. Multiplication by `d_Gamma` in (G3.3) is only a lattice inclusion;
later gaps in that ideal are obtained from new actual prime pairs.

## G4. Complete small residual coverage in rank r

**Lemma GP(r) (reserved prefix).** For each fixed constant `C`, one
reservoir can attain every signed native change in
`Gamma intersect [-CR,CR]^r` using

\[
 O_{K,C}(\ell^r\log R)=O_{K,C}(\ell^{r+1})                 \tag{G4.1}
\]

stages, with all endpoints distinct. A stage is supplied by one, two, or
four equal-gap pairs according to its spatial type.

**Proof.** Use dyadic scales `H_j=U/2^j` down to the last one in
`[C_r d_Gamma L,2 C_r d_Gamma L)`. At each scale apply DG with
`d=d_Gamma`. The resulting matrix `D_j` has columns in
`d_Gamma O subset Gamma`. Given the current lattice residual `v`, round
the `r` real coordinates of `D_j^{-1}v` to nearest integers. The new
residual has coordinate size at most `r H_j/2`. At the next scale its
previous size is at most `r H_j`; (G3.1) therefore bounds every integer
coefficient used by `O_{K,C}(L^r)`.

The final residual remains in `Gamma` and has size `O_K(d_Gamma L)`.
Its coordinates in the seed basis are integers and, by the sharper inverse
estimate in (G3.4), have size

\[
 O_K(L^{r-1}/d_\Gamma)\,O_K(d_\Gamma L)=O_K(L^r).
\]

There are `O(log R)` scales, proving (G4.1). Reserve twice each required
coefficient capacity in a direction, and begin with half of those stages
in each orientation. Selecting a subset realizes every needed signed
coefficient. At every later scale only a polynomial-logarithmic number
of fresh pairs is required; DG still gives `gg M/ell` after the entire
global reservation count is charged. The seed copies are taken from the
globally reserved seed matchings. Four-pair cuboids consume four distinct
members of a matching per stage. QED.

The doubled prefix has a center `p0 in Gamma` equal to half the sum of
its gaps. It realizes its bounded lattice box relative to `p0`. We will
use the coarse common stage envelope

\[
 P=\lceil\ell^{p_r}\rceil,\qquad p_r=r+10.                \tag{G4.2}
\]

Every prefix coordinate may have midpoint error `O(R)`; this is paid at
the full `O(PR)` per line. Prefix elements are not assumed near the mean.

## G5. Actual centered pairs and the finite residue operation

Fix `eta=ell^-c`. Translate the endpoint boxes of H2 to
`bar a +/- R vj/2`. Their positive domain margin persists because
`bar a/R -> u`. Every prime in them belongs to the exact initial pool,
even if its last norm tie is incomplete.

For a unit class `a mod q`, H3 gives at least

\[
 c_K\eta^rM/\varphi_K(\mathfrak q)                        \tag{G5.1}
\]

eligible entries in each box. Let `Nq<=ell^b`. After arbitrary prior
deletion of

\[
 Q=o(\eta^rM/\ell^b),                                    \tag{G5.2}
\]

a fixed positive fraction remains in every required box and class.

Differences between two such endpoint boxes lie in a prescribed coset of
`q` and in a box of radius `O(eta R)`. As `q=d_Gamma d_2` is a rational
scaling of a **fixed** ideal lattice, lattice counting bounds their number by

\[
 O_K(\eta^rR^r/N\mathfrak q).                             \tag{G5.3}
\]

All boundary terms are smaller, because `eta R/d_Gamma` tends to infinity.
No principal generator of `q` or class-number-one assumption is needed.
Pigeonholing the cross-box pairs yields at least

\[
 \gg_K\frac{\eta^rM N\mathfrak q}
                 {\varphi_K(\mathfrak q)^2\log R}
 \ge c_K\frac{M}{\ell^{rc+b+1}}                           \tag{G5.4}
\]

pairs with one common actual difference. The endpoint boxes are disjoint,
and for a fixed difference each endpoint has only one possible partner;
the pairs are already a matching. Each midpoint differs from `bar a` by
`O(eta R)`. With equal unit classes at the two ends, its gap belongs to
`q subset Gamma` and satisfies

\[
 \delta=Rv_j+O_K(\eta R).                                 \tag{G5.5}
\]

Take only the needed submatching, then repeat after its deletion. This
procedure never rotates, multiplies, or otherwise replaces a prescribed
input entry.

For modular routing we need differing unit classes. In any finite quotient
`O/q`, a class `Delta` is a difference of two units if and only if it is
zero at every norm-two prime ideal dividing `q`. Indeed, over a residue
field of size at least three, choose `a` outside `{0,-Delta}`; over `F2`
the only unit is one. Lift to prime-ideal powers and combine by CRT.
Each vector of a fixed integral basis of `d_2` obeys this criterion.
Using those two unit classes in the endpoint boxes gives (G5.4) in the
prescribed gap class. The actual gap has size `O(R)`, not necessarily
`O(eta R)`.

The quotient `d_2/q` is `(Z/d_Gamma Z)^r` in a fixed basis of `d_2`,
regardless of whether that ideal is principal. Reserve `d_Gamma-1`
switches per basis direction and per path/rectangle/body routing type.
Path prefix sums route a zero-total residue list, and double path prefix
sums route a zero-row/column-margin residue tensor. Reduce the `r`
coefficients modulo `d_Gamma`; the actual switches give exactly those
residues. Following the spatial correction order puts all line residuals
in `q subset Gamma`.

H4 and (G1.7) ensure the original errors belong to `d_2`. All later swaps
preserve that property. The residue phase costs `O_K(n^(D-1)d_Gamma)`
entries and `O_K(d_Gamma)` cells per required line, with actual numerical
line change `O_K(d_Gamma R)`. Every nonunit input at a different prime
ideal is still included; the controller has not assumed all input entries
are units modulo the adaptive modulus.

As an additional consequence, the additive group generated by all actual
differences of a sufficiently long prefix is exactly `d_2`: it contains
`Gamma`, hence `q`, and for every fixed basis vector `v` of `d_2` the
preceding actual gap is `v mod q`. Thus it contains `v`. The reverse
inclusion follows from H4. This argument proves an exact additive-group
statement without assuming that a seed lattice is itself an ideal.

## G6. A full rank-r zonotope and exact subset attainment

Let `K0` temporarily denote a positive capacity parameter tending to
infinity, not the number field. At each of the `r` fixed chord directions
take `J=ceil(C_* K0)` macro stages supplied by (G5.5), with a sufficiently
large fixed field/domain constant `C_*`. Denote their gaps by `delta_jt`.
They lie in `Gamma` and have size `O_K(R)`. The centered zonotope is

\[
 Z=\left\{\sum_{j,t}(s_{jt}-1/2)\delta_{jt}:0\le s_{jt}\le1\right\}.
\]

Since the `vj` form a fixed basis, some fixed `sigma>0` satisfies
`sum_j |w dot vj| >= sigma ||w||_1` for every real linear functional `w`.
The support function of `Z` is therefore at least

\[
 \frac{JR}{2}(\sigma-C_Kr\eta)\|w\|_1
 \ge\frac{JR\sigma}{4}\|w\|_1
\]

eventually. Choose `C_*>=16/sigma`, increasing fixed constants as needed.
By separation, `[-4K0R,4K0R]^r` lies in `Z`.

Let `S` be the total macro gap and round the `r` seed-basis coordinates
of `S/2` to obtain `q0 in Gamma` with

\[
 \|q_0-S/2\|_\infty\le\|G\|_\infty/2=O_K(\ell).         \tag{G6.1}
\]

For any `x in Gamma intersect [-K0R,K0R]^r`, the bounded feasible polytope

\[
 \sum_{j,t}s_{jt}\delta_{jt}=q_0+x,\qquad 0\le s_{jt}\le1
\]

is nonempty. At an extreme point at most **r** coefficients are strictly
between zero and one: otherwise those fractional columns have a nonzero
linear dependence permitting a small feasible perturbation of both signs.
Round those at most `r` coefficients. The remaining residual is in `Gamma`
and has size `O_K(rR)`. Choose the fixed prefix radius in GP(r) to cover
this constant times `R`. It realizes the residual exactly relative to `p0`.

**Lemma GZ(r).** A reservoir with `O_K(P+K0)` actual stages realizes the
entire lattice box `Gamma intersect [-K0R,K0R]^r` about a realizable
reference subset `p0+q0`. Its complement has the same signed capacity.
The native reference sums differ by only `O_K(ell)`. A fair choice between
them puts each of its physical pairs at the pair midpoint in expectation.

Every statement follows from the preceding construction and complementation
of all stage choices. In particular the residual prefix is not reused across
different actual reservoirs. A rectangle or cuboid stage complements all its
two or four pairs together. The `r` coordinates are a way to specify one
gap-vector demand; a feasible subset is one permutation of whole elements.
No separate coordinate permutations are introduced.

## G7. A complete explicit rank-dependent regime

The following exponents are sufficient for every fixed `r>=2`:

\[
 \begin{split}
 g&=r+10,&b&=r^2+2,&c&=5g,\\
 a_2&=rc+b+100,&a_1&=a_2+g,&a_0&=a_2+2g,\\
 a_3&=a_2-g,&h_r&=a_2+3g,&p_r&=r+10.                    \tag{G7.1}
 \end{split}
\]

Thus `a2=6r^2+50r+102` and `h_r=6r^2+53r+132`. These intentionally
loose exponents are a sufficient profile, not a numerical side-length
threshold and not an optimized estimate. Take

\[
 K_i=\lfloor n/\ell^{a_i}\rfloor\quad(0\le i\le3),
 \qquad\eta=\ell^{-c},\qquad P=\lceil\ell^{p_r}\rceil,
 \qquad H=nR/\ell^{h_r}.                                 \tag{G7.2}
\]

All floors are positive eventually; `K0<K1<K2<K3`. The four main quantitative
margins are explicit:

\[
 \begin{split}
 a_2-(rc+b)&=100 &&\text{(global deletion versus each endpoint box)},\\
 g-r&=10 &&\text{(ordinary vector-flow loss)},\\
 g-(r+2)&=8 &&\text{(tensor vector-flow loss)},\\
 (c+a_3)-h_r&=g>0 &&\text{(midpoint bias)}.                \tag{G7.3}
 \end{split}
\]

The fixed number `r` of cone families and basis directions, and all physical
one/two/four-pair multiplicities, are included in the constants below.

| Invoice | Square | Full signed cube |
|---|---:|---:|
| Main arithmetic reservoir types | `O_K(n)` | `O_K(n^2)` old plus `O_K(n)` signed |
| Total reserved entries `Q` | `O_K(nK2+K3+nP+nd_Gamma)` | `O_K(n^2K2+nK3+n^2P+n^2d_Gamma)` |
| Common eventual bound for `Q` | `O_K(M/ell^a2)` | `O_K(M/ell^a2)` |
| Seed copies required in each direction | `O_K(nP)` | `O_K(n^2P)` |
| Available seed matching per direction | `gg_K M/ell` | `gg_K M/ell` |
| Maximum per-line main load | `O_K(K3)` | `O_K(K3)` |
| Maximum per-line prefix/residue load | `O_K(P+d_Gamma)` | `O_K(P+d_Gamma)` |

For example `nK3/(n^2K2)=O(ell^g/n)` in the cube, and the same ratio
compares the diagonal term with the main square term. Also
`n^(D-1)P/(M/ell^a2)=O(ell^(p_r+a2)/n)`. Thus every lower-order invoice
really is absorbed by the stated common bound.

The boxes have pre-deletion supply `gg_K M/ell^(rc+b)` and one common
gap has matching supply `gg_K M/ell^(rc+b+1)`. The entire reservation
invoice has 100 powers of logarithmic slack against **each** box, uniformly
under arbitrary earlier deletion. Every new request can therefore take
its actual required one/two/four pairs. Only these pairs are removed;
reserving every available matching would exceed the invoice and is not done.
DG handles the prefixes after the same entire deletion count.

The combined seed demand is smaller than its original matching by the ratio
`O(ell^(p_r+1)/n)`. Finally `K3+P+d_Gamma=o(n)`, so every imported spatial
support-packing hypothesis holds, for both even and odd `n` once it is large.
These estimates also prove that all reserved endpoints are distinct before
the unused entries are assigned.

## G8. Whole-reservoir concentration and the unused-pool mean

Independently for each main reservoir choose its GZ(r) reference or its
complement with probability one half. Modular gadgets can retain fixed
reference states. Every macro cell has expected value within `O_K(eta R)`
of the actual mean `bar a`; every prefix or modular cell has error `O_K(R)`.
If line `L` has `s_L` reserved cells with sum `C_L`,

\[
 \|\mathbb E C_L-s_L\bar a\|_\infty
       =O_K(\eta K_3R+PR+d_\Gamma R).                     \tag{G8.1}
\]

One independent reservoir choice changes its native line sum by `O_K(ell)`,
its nonnative line sum by `O_K(R)` under the transverse support contract,
and a preserved line sum by zero. At most `O_K(K3+P+d_Gamma)` reservoirs
meet one required line. Hoeffding's inequality applied to whole-reservoir
variables, followed by a union bound over all `r` coordinates and every
required line, gives one joint reference choice with

\[
 \|C_L-s_L\bar a\|_\infty\le E,
 \quad E=O_K\left(\eta K_3R+PR+d_\Gamma R+
 R\sqrt{(K_3+P+d_\Gamma)\log n}\right).                    \tag{G8.2}
\]

The number of lines is `O(n)` for squares and `O(n^2)` for cubes; multiplying
by the fixed `r` changes only the union-bound constant. No independence
among lines or among coordinates is assumed.

There remain `M0=M-Q>=M/2` unused entries. Summing (G8.2) over one partition
into `n^(D-1)` axis lines gives

\[
 \left\|\sum_{\rm reserved}a-Q\bar a\right\|_\infty
       \le n^{D-1}E.
\]

Because `T=M bar a` is the **actual** total, the mean `bar a0` of the
remaining pool obeys

\[
 \|\bar a_0-\bar a\|_\infty\le2E/n.                     \tag{G8.3}
\]

Uniformly permute all unused entries among all unused cells. Each completed
line's expectation lies within `3E` of `mu`. Each coordinate of a pool
entry ranges over an interval of length `O_K(R)` by H1. The standard
sampling-without-replacement bounded-difference estimate and the same union
bound give a filler permutation with simultaneous errors at most

\[
 E_0=O_K\left(\eta K_3R+PR+d_\Gamma R+
 R\sqrt{(K_3+P+d_\Gamma)\log n}+R\sqrt{n\log n}\right)
       =o(H).                                             \tag{G8.4}
\]

For the first term, (G7.3) gives ratio `O(ell^-g)`. Prefix and residue
ratios are at most fixed logarithmic powers divided by `n`. Concentration
ratios are at most fixed logarithmic powers divided by `sqrt n`. These
conclusions hold for every fixed `r`, however slowly `R` grows.

All prescribed elements now occur exactly once. The modular phase of G5
changes each line by `O_K(d_Gamma R)=o(H)` and makes every residual a
member of `Gamma`, while preserving the necessary incidence congruences.
Main supports remain at their reference states until consumed below.

## G9. Integer flows and the cube tensor cost in arbitrary arithmetic rank

For a zero-total list of vector demands of size at most `W`, express its
entries in the seed basis and use integral bounded graph flows for each
of the `r` integer coordinate lists. Recombine the coefficients in `Gamma`.
The actual vector edge demand is bounded by

\[
 O_K(\kappa_G W+\|G\|_\infty)
       =O_K(\ell^rW+\ell).                               \tag{G9.1}
\]

The additive term includes the rounding of the integer capacity. All such
terms are negligible against the capacities in (G7.2).

For tensor correction use the frozen [IT theorem](controller.md), Section 7,
at scientific source `6f8524253c32db096e38715fd69e880e0fa85fdd`. If `B_G`
is the graph incidence matrix, every integer zero-margin matrix `D0` admits
integer coefficients with

\[
 B_GFB_G^{\mathsf T}=D_0,
 \qquad\|F\|_\infty\le(5\log n+5)^2\|D_0\|_\infty
                           +\tfrac12+32(n-1).             \tag{G9.2}
\]

For clarity, its additive linear bound comes from two integral flow stages:
round the real tensor solution, solve the bounded residual columnwise,
subtract its resulting circulation from one column to give zero row sums,
then solve those rows. With degree 64 and expansion 8 the first flow cap
is 256 and the second is `32(n-1)`. This is a geometric integer theorem
independent of the coefficient ring. The old `512n^2` remainder would not
suffice in general rank and is not used.

Apply (G9.2) to the `r` seed-coordinate matrices of a vector residual matrix
of size at most `W`, then recombine. Its vector rectangle demands have size

\[
 O_K(\ell^{r+2}W)+O_K(n\ell).                            \tag{G9.3}
\]

The second term remains small relative to the level-2 capacity in **every
fixed arithmetic rank**:

\[
 \frac{n\ell}{K_2R}
       =O_K\left(\frac{\ell^{a_2+1}}R\right)
       \longrightarrow0,
 \qquad R\asymp_K n^{D/r}(\log n)^{1/r}.                 \tag{G9.4}
\]

This is the decisive scaling check. No assumption such as `r<6` or
`R>n` is required. A positive fixed power `n^(D/r)` dominates every
fixed logarithmic power. The argument is not uniform when `r` grows with
`n`; in that regime (G9.4) need not follow.

## G10. Completing every required line with one permutation

### Squares

The initial centered and residue-corrected row and column demands have size
`O(H)` and zero total. Their edge demands from (G9.1) have size
`O(ell^r H+ell)=o(K2R)`. The level-2 reservoirs consume these vector
demands. Row operations preserve columns and both diagonals; column
operations preserve rows and both diagonals. The two diagonal errors remain
`O(H)` and are consumed by their isolated level-3 rectangle reservoirs.
Each preserves both axis directions and the other diagonal. All `2n+2`
required targets are attained.

### Full signed cubes

1. **Plane totals.** They have zero-total residuals of size `O(nH)`.
   Their graph vector flows cost `O(ell^r nH+ell)`. Split each integer
   seed-coordinate edge demand among its `n` parallel level-0 reservoirs,
   as evenly as possible. Recombination gives size
   `O(ell^r H+ell)=o(K0R)` per reservoir, since `h_r-a0=g>r`.
   All plane totals become exact; vertical sums are preserved, and
   remaining horizontal line errors are `O(K0R)` by their separate load cap.
2. **Two slice directions.** In each plane, their two residual lists have
   exact total zero. The vector flows cost
   `O(ell^r K0R+ell)=o(K1R)` because `a0-a1=g>r`.
   Level-1 row and column reservoirs preserve one another. Both horizontal
   axis families become exact; each vertical residual is `O(K1R)`.
3. **Vertical tensor.** Its residual matrix has exact zero row and column
   margins. By (G9.3) every vector rectangle demand is
   `O(ell^(r+2)K1R)+O(n ell)=o(K2R)`. The first ratio is `O(ell^-8)`
   by (G7.3); the second is (G9.4). Level-2 rectangles consume the demands
   without changing the fixed horizontal directions. All axes are exact.
4. **Bodies.** The old numerical supports avoid them, so their errors
   remain `O(H)`. The four isolated level-3 cuboid reservoirs attain their
   targets while preserving every axis and the other bodies. Fresh
   reflection orbits keep each face-line drift at `O(R)`.
5. **Faces.** Old face loads left errors of size `O(K2R)`; the body drift
   does not increase this order. Each of the six residual families has
   total zero by its diagonal-square compatibility identity. Vector graph
   flows cost `O(ell^r K2R+ell)=o(K3R)` because `a2-a3=g>r`.
   The level-3 face reservoirs preserve all axes, all bodies, and the
   other five face families while attaining the chosen family.

Every one of the `3n^2+6n+4` full signed-coordinate line targets is now
attained. At each step GZ(r) decodes one recombined vector demand into
one subset of actual stage flips. All supports and all endpoints were
already mutually disjoint. The process is therefore one permutation of
the prescribed whole elements, not `r` separately assembled arrays.
This proves GC(r). QED.

## G11. Consequences, genuine hypotheses, and scope limits

The proof shows that **arithmetic rank alone is not an obstruction** to the
square or full signed-cube architecture. For every fixed rank, all new
losses are fixed logarithmic powers and fixed multiplicative constants.
The only polynomial additive tensor loss is `O(n ell)`, which (G9.4)
pays for every fixed rank. General rank changes the conditioning, the
modulus norm exponent, the number of extreme-point fractional coordinates,
and the global supply invoice; none is left as an analogy.

For a prime-array corollary, one must separately supply compatible prime
targets with the exact total `T`, in a window `o(H)`, and the target
congruence in (G1.7). Fixed-system ternary completion in `2r` integer
variables is compatible with this proof; an exponent larger than `h_r`
can be chosen once the field is fixed. No growing family of analytic
forms is licensed. The number-field target theorem and the canonical
domain/centroid proof must be verified for the chosen field and pool.

Class number greater than one is not a physical-controller obstruction.
H1 permits its fixed principal-prime density factor, H3 counts actual
prime elements, and the sole adaptive ideal here is a rational multiple
of fixed `d_2`. Neither its principality nor free multiplication of
physical gaps is used. Likewise infinite units are not resolved by this
controller: they are resolved by proving a full-unit normalization and H2
for the frozen pool before invoking it.

H4 is substantive. If a frozen pool retains an exceptional norm-two prime
element, it is not legitimate to delete that entry to satisfy this theorem.
In the rational field, the convention "omit only ramified prime classes"
omits none and retains 2. For every `n>=2` and `D>=2`, an array of its
first `n^D` positive rational primes cannot have all axis sums prime:
every such sum exceeds 2, so summing one axis partition would give total
parity `n^(D-1)`, whereas the input total has parity `n^D-1`; these differ
for both even and odd `n`. Omitting 2 gives the familiar different odd-prime
model. This is a genuine pool-dependent obstruction, not a failure of the
rank calculation. The cyclotomic arithmetic audit must establish H4 for
its own fields; it may not infer it from the absence of a numerical example.

Finally, a nonempty support and a density theorem alone do not imply H2.
The reflected interior intersection is the condition that produces actual
centered endpoint pairs. If that condition fails for a different unit
normalization, GC(r) does not silently replace the pool with one having
better geometry. A balanced multipair theorem or another separately proved
mechanism would then be required.

No explicit numerical side-length cutoff, efficient implementation of the
full asymptotic construction, growing-rank theorem, or uniformity over all
conductors is asserted. The threshold is allowed to depend on the fixed
field, unit-domain choice, and the exponents (G7.1), and to inherit the
analytic input's ineffectivity. The inequalities hold on a complete tail,
not merely on an unbounded subsequence.
