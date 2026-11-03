# A rank-four physical controller and a smaller integral tensor correction

Author: `/root/controller`. All labels are manuscript-local; no permanent
claim identifiers are allocated. This manuscript proves the physical transfer
from the frozen pool geometry and prime-box interface, with those dependencies
stated explicitly. Independent review must be recorded against its actual
source revision, separately from its mathematical status.

## 1. Scope, imports, and the physical theorem

The fields are the three fixed quartic cyclotomic fields in the canonical
problem definition. Arithmetic coordinates always mean the integral basis
`(1,zeta,zeta^2,zeta^3)`, hence have rank `r=4`. Array dimension is `D=2` or
`D=3`; it determines the cell geometry, not the number of coordinates of an
entry. Let

\[
 A=A(n,D),\quad M=n^D,\quad B=\max_{a\in A}|N(a)|,
 \quad R=B^{1/4},\quad T=\sum_{a\in A}a,\quad m=T/M,
 \quad\mu=nm,\quad\ell=\log R.
\]

The following three inputs are used and must be proved for the selected pool.

1. **Pool scale and boundedness.** `A` is the exact norm-ordered initial pool,
   including higher residue degree primes and the possible cut final tie;
   `M asymp R^4/log R`; and all coefficient coordinates of its elements have
   absolute value at most `C R`. In the Minkowski coordinates `(z1,z2)`,
   `m/R` tends to `(c,0)` with `3/4<c<5/6`.
2. **Centered interior endpoint boxes.** There are four fixed real-linearly
   independent Minkowski gaps `v1,...,v4`, with fixed bounded condition
   number, such that the two points `(c,0) +/- vj/2` are strict interior
   points of the canonical norm-less-than-one domain. A fixed neighborhood
   of every endpoint remains inside that domain. For the log-unit pool,
   this follows from the antipodal construction in Section 2 below.
3. **Uniform prime-box input.** For fixed positive `a,b`, any required
   coefficient box of radius `R/(log R)^a` around those endpoint points,
   and every unit class modulo an ideal of norm at most `(log R)^b`, has
   at least a constant times `R^4/((log R)^(4a+1) phi(q))` prime elements.
   Those elements are already canonical representatives and lie strictly
   below the cutoff. The estimate is uniform under the adaptive box and
   residue choices. The analytic source proves this from the stated fixed
   field prime-distribution theorem, retaining its ineffectivity.

Put

\[
 \mathcal D=O\quad(m=5,12),\qquad
 \mathcal D=(1-\zeta_8)O\quad(m=8).
\]

The normalization/local manuscript establishes that every element of the
eighth-root pool has residue one modulo `D`, while in the other fields there
is no norm-two prime ideal. The only finite residue fact used in the
controller is: a class `Delta mod q` is a difference of two units exactly
when it is zero at all norm-two prime ideals dividing `q`. This is the
elementary finite-field/CRT lemma proved in Section 5.

**Theorem PC4 (physical transfer; proved from Inputs 1--3).** For either
array dimension and all sufficiently large `n`, every compatible integral
line-target vector within

\[
 H=nR/\ell^{1120}                                             \tag{1}
\]

of `mu`, coordinate by coordinate, is realized by a permutation of exactly
`A`, provided every target is congruent to `n` modulo `D`. When `D=O`, this
last condition is empty. Compatibility means equality of row and column
totals with `T` for squares; for cubes it means all axis plane-marginal
identities, directional total `T`, and the six slice-diagonal-family total
identities. No extra equation is imposed on the body diagonals for the
sufficiently large orders used here.

This is a single permutation of whole elements, not four independent
coordinate permutations. The theorem allows repeated target values. It does
not require the targets themselves to be canonical representatives.

The arithmetic-independent support imports are pinned as follows:

* quadratic scientific source `e6e581efb9b676a7d5bc88b91c01571b087ed5da`,
  `problems/quadratic-prime-arrays/manuscripts/vector_controller.md`, Section 5
  (one/two/four-pair support contracts and simultaneous placement), and
  `local_arithmetic.md` (even-order full signed-cube incidence extension);
* ordinary scientific source `a2445962ec6e06b2a893980fb7a183057eb9bcee`,
  `problems/prime-arrays-beyond-square/manuscripts/{signed_trades,signed_cube,
  cube_controller,incidence}.md`, with the exact sections listed in the
  quadratic source;
* scalar square support source `c2118dfad1aeb660d66308dc6a94d6c959f5010c`,
  `problems/prime-line-sums/manuscripts/explicit_controller.md`, Section 3.

Only their graph, incidence, support-placement, and integer-flow assertions
are imported. The rank-two prime supply, planar radius law, and tensor
rounding invoice are not transferred. Sections 3--10 below supply their
quartic replacements. These imports are conventional mathematical arguments,
not claims of kernel verification.

## 2. Centered endpoints when the mean is outside the support

The normalized canonical log domain has coordinates

\[
 z_1=\rho e^{t/2}e^{i\theta_1},\qquad
 z_2=\rho e^{-t/2}e^{i\theta_2},\qquad
 0<\rho<1,\quad -L<t<L,
 \quad -a<\theta_1<a,\quad \theta_2\in\mathbb R/(2\pi\mathbb Z),
                                                               \tag{2}
\]

away from its half-open boundary. Here `L>0` is the frozen log-unit length
and `a=pi/w`. The normalization source proves the centroid `(c,0)` and
`3/4<c<5/6`. That centroid is outside (2), because its second component
vanishes. No neighborhood of the mean can be declared to contain canonical
prime entries.

Nevertheless

\[
 a_-=(c,-c),\qquad a_+=(c,c)                                  \tag{3}
\]

are both strict interior points: `rho=c<1`, `t=0`, and `theta1=0`.
They have midpoint `(c,0)`. Consequently the set

\[
 \{v:(c,0)-v/2\text{ and }(c,0)+v/2\text{ belong to (2)}\}
                                                               \tag{4}
\]

contains a full-dimensional open ball around `(0,2c)`. It therefore
contains four real-linearly independent vectors with a positive fixed
least singular value. For an explicit choice in real coordinates
`(Re z1,Im z1,Re z2,Im z2)`, take `v0=(0,0,2c,0)` and, for a sufficiently
small fixed positive `epsilon`, take

\[
 v_1=v_0,\quad v_2=v_0+\epsilon e_1,
 \quad v_3=v_0+\epsilon e_2,
 \quad v_4=v_0+\epsilon e_4.                                \tag{5}
\]

Their determinant has absolute value `2c epsilon^3`. Small fixed `epsilon`
makes all eight endpoints strict interior points. The fixed real-linear
change to coefficient coordinates preserves independence and replaces its
condition bound by another field-dependent constant.

For the actual pool mean, replace `(cR,0)` by `m`. Since `m/R` converges
to `(c,0)`, all endpoint boxes of radius `eta R`, centered at
`m +/- R vj/2`, stay in the domain and below a fixed strict norm fraction of
`B` once `R` is large. Their pair midpoints are within `eta R` of the
**actual** mean in all four coordinates. Thus centered actual pairs exist
without placing either endpoint near the mean, changing the pool, or
rescaling any entry by a unit.

## 3. Independent repeated gaps from density alone

The elementary density statement is given in general fixed rank. Constants
depend only on that rank. No prime-pair conjecture or prime-distribution
theorem is used in it.

**Lemma DG.** For fixed `r>=2`, there are constants `C_r,c_r>0` such that
the following holds. Let

\[
 A\subset[-U,U]^r\cap\mathbb Z^r,\quad s=|A|\ge U^r/L,
 \quad L\ge2,\quad d\in\mathbb Z_{>0},
 \quad C_r dL\le H\le U.
\]

There are independent differences `g1,...,gr` in `d Z^r`, each of maximum
coordinate size at most `H`, with

\[
 |\det[g_1\ \cdots\ g_r]|\ge(H/(C_rL))^r,
 \qquad\|[g_1\ \cdots\ g_r]^{-1}\|_\infty
       \le C_r L^r/H,                                      \tag{6}
\]

and at least `floor(c_r s/L)` pairs of each gap. All pairs in all `r`
families can be chosen mutually disjoint.

**Proof.** Partition the coefficient cube into half-open cubes of side
`H`, then partition each by its coordinate residues modulo `d`. There are
at most `(4U/H)^r d^r` groups. If their sizes are `s_j`, Cauchy--Schwarz
gives at least

\[
 P=\sum_j s_j(s_j-1)
 \ge s^2H^r/(4^rU^rd^r)-s
 \ge sH^r/(2\cdot4^rd^rL)                                 \tag{7}
\]

ordered pairs, with the last inequality ensured by increasing `C_r`.
There are at most `(3H/d)^r` possible differences.

For every proper linear subspace `W`, choose a containing hyperplane and
a unit normal with some coordinate of absolute value at least `1/sqrt r`.
Fixing the other `r-1` coordinates shows that the number of lattice
differences in `[-H,H]^r` at Euclidean distance at most `h` from that
hyperplane is at most

\[
 (2H/d+1)^{r-1}(2\sqrt r\,h/d+1).                          \tag{8}
\]

Take `h=H/(A_r L)` with a temporary rank-dependent constant `A_r`;
its ratio to `d` is at least one when the scale constant is sufficiently
large. Choose `A_r` so that (8) is less than `H^r/(4*4^r d^r L)`.
Each difference accounts for at most `s` ordered pairs. At least half
the pairs in (7) therefore have difference at distance greater than `h`
from `W`. Some such gap occurs at least `s/(4*12^r L)` times.
Apply this successively to the spans of the already selected gaps. Their
Gram--Schmidt distances exceed `h`. The adjugate estimate gives inverse
bound `r! A_r^r L^r/H`. Now take the statement's `C_r` at least both
`A_r` and `r! A_r^r`, as well as the earlier scale constant. This proves
both bounds in (6) without identifying the temporary constants.

A fixed nonzero gap has a pair graph of maximum degree two. Its edges
have a matching of size at least one third of their number. Select
`k=floor(s/(100 r 12^r L))` pairs for each successive gap. Earlier
families delete at most `2(r-1)k` vertices, hence at most `4(r-1)k`
edges of the next graph. More than `3k` edges remain, so the next
matching can be chosen. This proves simultaneous disjointness. QED.

Any arbitrary prior deletion leaving the density hypothesis valid is
allowed. At rank four, `U=C R`, `L=C' ell`, and total deletion `o(M)`
satisfy it. In particular every selected gap has a matching of size
`gg M/ell` after the global reservation invoice is charged.

Choose seed scale `H_s=ceil(C_4 L)` and apply DG with `d=1`. Let

\[
 G=[g_1\ g_2\ g_3\ g_4],\quad\Gamma=G\mathbb Z^4,
 \quad d_\Gamma=|\det G|,\quad q=d_\Gamma\mathcal D.
\]

The seed gaps are actual differences of pool elements, so `Gamma subset D`.
The exact index in `O` is `d_Gamma`, and the adjugate identity gives

\[
 q\subseteq d_\Gamma O\subseteq\Gamma\subseteq\mathcal D,
 \qquad d_\Gamma=O(\ell^4),
 \quad\|G\|_\infty=O(\ell),\quad
 \|G^{-1}\|_\infty=O(\ell^3),\quad\kappa_G=O(\ell^4).
                                                               \tag{9}
\]

This is an additive lattice construction; `Gamma` need not be an ideal.
The contained ideal `q` has norm `O(ell^16)`, hence at most `ell^20`
eventually. No physical multiplication of a seed pair is used.

## 4. A finite prefix giving complete lattice coverage

**Lemma PF.** For each fixed `C>0`, a reservoir of
`O_C(ell^4 log R)` signed copies of actual gaps can attain every vector
in `Gamma` whose maximum coordinate size is at most `C R`. Each copy
can be supplied as one, two, or four equal-gap pairs as its spatial support
requires. All endpoints can be chosen distinct.

**Proof.** Use dyadic scales `H_j=U/2^j` down to a last scale between
`C_4 d_Gamma L` and twice that number. At each scale apply DG with
`d=d_Gamma`, obtaining a matrix `D_j` of four actual gaps in
`d_Gamma O subset Gamma`. For residual `v`, round the four coordinates
of `D_j^{-1}v` to nearest integers. The new residual has size at most
`2H_j`. The first coefficient vector and all later ones have size
`O_C(L^4)` by (6), because the previous residual is at most `4H_j`.
The final residual is still in `Gamma`. Its integer `G`-coordinates have
size at most

\[
 O(H_s^3/d_\Gamma)\,O(d_\Gamma L)=O(L^4).
\]

Thus `O_C(L^4)` signed copies per dyadic scale and in the seed directions
suffice. Reserve twice each required absolute coefficient bound, starting
half in each orientation. A binary switch with gap `g` then realizes all
integer signed coefficients between the two capacity endpoints. Each
dyadic request has `gg M/ell` fresh pairs available, while the required
number is polynomial in `ell`; seed copies are reserved globally from the
initial matchings. The same coefficient algorithm acts on one vector gap
at a time. It does not replace an element by its coordinate projections.
QED.

The prefix center is exactly half the sum of its gap vectors and belongs
to `Gamma`, because every directional multiplicity was doubled. We use
the convenient eventual stage envelope

\[
 P=\lceil\ell^{100}\rceil.                                 \tag{10}
\]

Its entries may come from anywhere in the pool. Its possible centering
error is therefore charged at full size `O(PR)` per line.

## 5. Actual centered equal-gap tuples and modular routing

Let `eta=ell^-200`, so `4c+B+1=821` for `c=200`, `B=20`. Put two
coefficient boxes of radius `eta R` at the endpoints from Section 2.
For any unit classes `a,b mod q`, Input 3 supplies

\[
 \gg\eta^4M/\varphi_K(q)                                  \tag{11}
\]

points in each box. Every prescribed-pool deletion of size
`o(eta^4 M/N(q))` leaves a fixed positive fraction of this count.
For each ordered cross-box pair its difference lies in the prescribed
coset `b-a mod q`. Since `q=d_Gamma D` is a rational scaling of one
fixed ideal lattice, the number of possible differences in their bounding
box is

\[
 O(\eta^4R^4/N(q)).                                       \tag{12}
\]

Boundary terms are smaller since `d_Gamma` is polynomial-logarithmic
and `eta R/d_Gamma` tends to infinity. Pigeonholing gives one common
actual gap and at least

\[
 \gg\frac{\eta^4M N(q)}{\varphi_K(q)^2\log R}
 \ge c_K M/\ell^{821}                                    \tag{13}
\]

pairs. For a fixed gap these form a matching: the two boxes are disjoint,
and each endpoint has exactly one possible partner. Every pair midpoint
is within `eta R` of the actual mean, and the gap is within `2 eta R`
of the selected fixed macroscopic direction times `R`.

For the main controller choose `a=b=1`, giving gaps in `q subset Gamma`.
For modular routing choose arbitrary allowed difference `Delta`.
In a residue field of cardinality `Q>=3`, choose `a` outside
`{0,-Delta}`; then `a,a+Delta` are nonzero. In a field of two elements,
their difference must be zero, and this condition is sufficient. Lifting
to prime ideal powers and applying CRT proves the stated unit-difference
criterion. Each fixed integral basis vector of `D` obeys it for `q`.
Four actual equal-gap pairs, in the prescribed difference class, are
available from (13); one or two can be used for the simpler support types.

Reduce the four `D`-basis coordinates of an error modulo `d_Gamma`.
Path prefix sums route zero-total lists, and double path prefix sums route
zero-row/column-margin matrices, just as in the scalar support imports.
For each basis direction reserve `d_Gamma-1` actual switches per routing
type. Their gaps have the required class modulo `q`, so after routing
every line residual is in `q subset Gamma`. The order is rows, columns,
diagonals for squares, and planes, slice axes, remaining axis tensor,
bodies, then faces for cubes. The imported incidence identities ensure
the relevant zero-total/zero-margin hypotheses at every stage.

These routing gaps have size `O(R)`, even when the mean has a zero second
embedding. Their cost is therefore `O(d_Gamma R)` per line. We do not
claim that their endpoints, or their gaps, lie in a small neighborhood
of zero. The total routing uses `O(n^(D-1)d_Gamma)` cells, with `O(d_Gamma)`
cells on each required line under the bounded-degree support placement.

## 6. Zonotope rounding with four fractional coordinates

Fix a sufficiently large integer `K`. For each of the four macro cones
reserve `J=ceil(C_K K)` stages, with `C_K` a fixed field-dependent
constant chosen below. Write their gaps as `delta_jt`. They belong to
`Gamma`, have size `O(R)`, and satisfy

\[
 \|\delta_{jt}-Rv_j\|_\infty\le2\eta R.                    \tag{14}
\]

The centered zonotope is

\[
 Z=\left\{\sum_{j,t}(u_{jt}-1/2)\delta_{jt}:0\le u_{jt}\le1\right\}.
\]

Because the fixed matrix with columns `vj` is invertible, there is a
fixed `sigma>0` such that `sum_j |w dot vj|>=sigma ||w||_1` for all
real linear functionals `w`. Its support function consequently satisfies

\[
 h_Z(w)\ge(JR/2)(\sigma-8\eta)\|w\|_1
          \ge(JR\sigma/4)\|w\|_1
\]

eventually. Choose `C_K>=16/sigma`. The support-function separation
criterion gives the box `[-4KR,4KR]^4 subset Z`.

Let `p0` be the prefix center, exactly half its doubled gap sum, and
let `S` be the sum of macro gaps. Round the four `G`-coordinates of
`S/2` to obtain `q0 in Gamma`, with
`||q0-S/2||_infty<=||G||_infty/2=O(ell)`. For every
`x in Gamma cap [-KR,KR]^4`, there is a feasible real vector `u` in
`[0,1]` with `sum u_jt delta_jt=q0+x`. Choose an extreme point of this
bounded feasible polytope. At most four coordinates are fractional:
five fractional columns admit a nonzero linear dependence and therefore
a small feasible perturbation of both signs, contradicting extremality.
Round those at most four coordinates. The residual is in `Gamma` and
has size at most `C'R`, for a fixed field-dependent `C'`.
Lemma PF realizes it exactly relative to `p0` using the separately
reserved prefix. Thus the resulting full subset sum is `p0+q0+x`,
and the first complete reference is `p0+q0`.

**Lemma Z4 (complete physical reservoir).** The prefix and macros have
a realizable reference subset within `O(ell)` of half their total gap.
From that reference, and from its complementary subset, every native
vector change in `Gamma cap [-KR,KR]^4` is attainable. The reservoir
has `O(P+K)` stages. A fair random choice between the two references
puts every physical pair at its actual midpoint in expectation.

The proof above establishes the first reference; complementing all
chosen stages establishes the second and the same symmetric capacity.
Their native sums differ by only `O(ell)`. Complementing a rectangle or
cuboid switches all its two or four pairs together. Thus all four
arithmetic coordinates and all simultaneous spatial side effects arise
from one actual subset of legal whole-element swaps. A real spanning
argument without the separately reserved prefix would not prove this
integer attainability statement.

## 7. An integral tensor correction of order n, not n squared

The quadratic controller imported a tensor coefficient bound with additive
loss `512 n^2`. At quartic cube scale `R asymp n^(3/4)(log n)^(1/4)`,
`K R` for `K=n/polylog(n)` is too small to absorb that loss. The following
replacement is therefore needed; it is not an optional numerical improvement.

**Lemma IF (integral expander flow).** Let a connected loopless multigraph
have edge expansion at least `h>0`. If an integer vertex vector `v` has
sum zero and maximum absolute coordinate at most `delta`, there is an
integer edge flow with divergence `v` and absolute edge coefficients at
most `ceil(delta/h)`.

For any cut `S`, the required net flow is at most
`delta min(|S|,|S^c|)`, while the cut has at least
`h min(|S|,|S^c|)` edges. Give both orientations of every edge capacity
`ceil(delta/h)` and add source/sink arcs for the vertex demands. Every
cut has sufficient capacity. The augmenting-path proof of integral
max-flow therefore gives a feasible integer flow. Subtract opposite
directed flows to obtain the stated signed coefficients.

**Theorem IT (improved integer tensor coefficients).** Suppose the graph
also has degree at most `Delta` and the real right inverse in the pinned
tensor-expander theorem has infinity norm at most `L_G`. Let `B_G` be its
oriented incidence matrix. For every integer zero-row/column-margin
matrix `D0`, there is an integer matrix `F` with

\[
 B_G F B_G^{\mathsf T}=D_0,
\quad\|F\|_\infty\le L_G^2\|D_0\|_\infty+\tfrac12
       +\left\lceil\frac{(n-1)\lceil\Delta^2/(2h)\rceil}{h}\right\rceil.
                                                               \tag{15}
\]

**Proof.** The pinned real construction gives `F0` of norm at most
`L_G^2 ||D0||`. Round it entrywise to nearest integers `F1`. The integer
residual

\[
 H_0=D_0-B_G F_1 B_G^{\mathsf T}
\]

has zero margins and coordinate size at most `Delta^2/2`: each entry
sees at most `Delta^2` rounding errors of size at most one half.
For each column solve `B_G U_j=(H0)_j` using IF, with edge bound
`b=ceil(Delta^2/(2h))`. Put `s=sum_j U_j`. Since the row sums of `H0`
are zero, `B_G s=0`. Subtract `s` from the last column of `U`, keeping
every other column unchanged. Call the result `U'`. It still satisfies
`B_G U'=H0`, now has every row sum zero, and has entry bound
`(n-1)b`; its last column is exactly minus the sum of the first `n-1`.
For each row of `U'`, apply IF again. The resulting integral matrix `C`
satisfies `C B_G^T=U'` and has entry bound `ceil((n-1)b/h)`.
Then `F=F1+C` proves (15). QED.

For the imported degree-64, expansion-8 graphs,

\[
 L_G\le5\log n+5,
 \qquad\|F\|_\infty\le(5\log n+5)^2\|D_0\|_\infty
                         +\tfrac12+32(n-1).               \tag{16}
\]

No entry- or gap-size assumption occurs in this lemma. The proof uses
only integer graph flows, and is finite. It improves exactly the place
where the original tree-product correction summed a bounded residual
over a product of two cuts of size `O(n)`. The anchoring in the first
flow stage is paid explicitly and costs only one factor of `n`.

## 8. Spatial supports and one consistent parameter regime

Use the fixed bounded-degree expander graphs supplied by the pinned
geometric construction, and take

\[
 \begin{split}
 K_0&=\lfloor n/\ell^{1100}\rfloor,&
 K_1&=\lfloor n/\ell^{1050}\rfloor,\\
 K_2&=\lfloor n/\ell^{1000}\rfloor,&
 K_3&=\lfloor n/\ell^{950}\rfloor,\\
 \eta&=\ell^{-200},&P&=\lceil\ell^{100}\rceil.
 \end{split}                                               \tag{17}
\]

All floors are positive eventually. These are a sufficient asymptotic
regime with fixed exponents; they are not an explicit numerical cutoff.

The support contracts are unchanged identities over any additive group:
one pair for an ordinary transfer, two simultaneous equal-gap pairs for
a rectangle, four for a cuboid. A rectangle has signed cell changes
`delta [[1,-1],[-1,1]]`; a cuboid has changes
`delta (-1)^(i+j+k)` on its eight vertices. The equal gap is an equality
of all four coefficient coordinates. The same fixed finite factor is
charged for every arithmetic direction and every prefix copy.

For squares, use row and column edge reservoirs at level 2 and one
isolated rectangle reservoir per long diagonal at level 3. Place the
diagonal bundles first, with fresh rows and columns, then row/column
passes avoiding both diagonals. The imported degree and transverse caps
give `O(K3+P+d_Gamma)` cells per required line, and disjoint supports
whenever that count is `o(n)`.

For cubes, use `n` level-0 reservoirs per edge between planes; level-1
row and column edge reservoirs in each plane; one level-2 rectangle
reservoir for each pair of edges in the two transverse graphs; level-3
body cuboids; and level-3 face-family edge reservoirs. The old axis
passes avoid the body diagonals. Every body stage uses fresh reflection
orbits globally, which limits its total drift on any fixed face line to
`O(R)`. Each face reservoir preserves axes, bodies, and the other five
face families. Prefix, main, and modular passes are placed separately
with the same caps. The even-order extension needs five noncentral
reflection orbits, available for all `n>=10`; no arithmetic parity was
used by that placement argument.

The invoices, including all four arithmetic directions, are

| Quantity | Square | Full signed cube |
|---|---:|---:|
| Main reservoir types | `O(n)` | `O(n^2)` old and `O(n)` signed |
| Total reserved entries | `O(nK2+K3+nP+nd_Gamma)` | `O(n^2K2+nK3+n^2P+n^2d_Gamma)` |
| Common eventual deletion bound | `O(M/ell^1000)` | `O(M/ell^1000)` |
| Seed copies required per direction | `O(nP)` | `O(n^2P)` |
| Available seed matching | `gg M/ell` | `gg M/ell` |
| Maximum line load | `O(K3+P+d_Gamma)` | `O(K3+P+d_Gamma)` |

The smaller endpoint boxes have before-deletion count `gg M/ell^820`,
and matching count `gg M/ell^821` by (13). The **entire** eventual
global deletion bound `Q=O(M/ell^1000)` is smaller than each required
box count. Therefore every adaptive request can still take its actual
one/two/four fresh pairs. Only those pairs, not its entire matching,
are removed. Density-only prefixes survive the same deletion count.
All seed copies are reserved first. At all times the pool is exactly
the frozen one, and its unused elements remain available as filler.

For both spatial dimensions, `K3+P+d_Gamma=o(n)`, so the geometric
placement hypotheses hold. The arithmetic scales are

\[
 R\asymp n^{1/2}(\log n)^{1/4}\ (D=2),\qquad
 R\asymp n^{3/4}(\log n)^{1/4}\ (D=3).                    \tag{18}
\]

In particular `log R asymp log n`. No planar radius law is used.

## 9. Centering after all reservations

For each main reservoir independently choose its Z4 reference or its
complement with probability one half. Every main cell then has expected
value within `eta R` of the actual mean `m`. Prefix and modular cells
are charged at `O(R)` each. If a required line contains `r_L` reserved
cells with sum `C_L`,

\[
 \|\mathbb E C_L-r_Lm\|_\infty
       =O(\eta K_3R+PR+d_\Gamma R).                        \tag{19}
\]

A whole-reservoir choice changes a native line by `O(ell)` from Z4;
a nonnative line by `O(R)` under the bounded transverse-intersection
contract; and a preserved line by zero. The number of reservoirs that
meet a line is at most its `O(K3+P+d_Gamma)` reserved-cell count.
Hoeffding's inequality in each of four coordinates, with a union bound
over every square or full signed-cube line, yields a joint choice with

\[
 \|C_L-r_Lm\|_\infty\le E,
 \quad E=O\left(\eta K_3R+PR+d_\Gamma R+
 R\sqrt{(K_3+P+d_\Gamma)\log n}\right).                    \tag{20}
\]

The independent random variables are whole reservoir orientations.
Neither lines nor four coordinates are treated as independent objects.

There are `M0>=M/2` unused elements. Sum (20) over one partition into
axis lines and use the exact pool total. The unused-pool mean `m0`
satisfies `||m0-m||<=2E/n`. Uniformly permute all unused elements into
all unused cells. The expected completed line differs from `mu` by
at most `3E`. Sampling-without-replacement bounded differences and the
same four-coordinate union bound give a complete filler permutation
whose errors are at most

\[
 E_0=O\left(\eta K_3R+PR+d_\Gamma R+
 R\sqrt{(K_3+P+d_\Gamma)\log n}+R\sqrt{n\log n}\right)=o(H).
                                                               \tag{21}
\]

Indeed the first term is `nR/ell^1150`, whereas `H=nR/ell^1120`;
every other ratio is a fixed logarithmic power times a negative power
of `n`. The modular routing subsequently changes lines by only
`O(d_Gamma R)=o(H)`, and puts all residuals in `Gamma`.
At this point every prescribed prime element has been used exactly once.

## 10. Consuming the capacities, including all cube lines

For a square, the row and column residual lists each have sum zero.
Solve integral flows in the four `G`-coordinates and recombine to vector
demands. Their size is `O(kappa_G H)=O(ell^4 H)=o(K2 R)`.
Their level-2 reservoirs realize those demands, preserving the other
axis direction and both diagonals. The two remaining diagonal errors
are `O(H)`; their isolated level-3 rectangle reservoirs fix them while
preserving both axis families and the other diagonal. This proves PC4
for squares.

For cubes, use the following sequence; every reservoir is still at its
chosen reference when consumed.

1. **Plane totals.** The zero-total list has residual size `O(nH)`.
   Its four integral flows have vector edge demand `O(kappa_G nH)`.
   Split each of the four integer basis coefficients among the `n`
   parallel level-0 reservoirs as evenly as possible. Each vector demand
   has size `O(kappa_G H+||G||)=o(K0 R)`. The plane totals become exact;
   all vertical axis sums remain fixed, and the remaining horizontal
   errors are `O(K0 R)` by their load caps.
2. **Two slice directions.** In each plane, the two zero-total residual
   lists cost `O(kappa_G K0 R)=o(K1 R)`. Their level-1 graph flows
   preserve one another. All horizontal axis targets become exact,
   and each vertical error has size `O(K1 R)`.
3. **Vertical tensor.** The remaining vertical residual matrix has zero
   row and column margins. Express it in the four `G`-coordinates and
   apply (16) to each coordinate matrix. Recombine the four integer
   coefficient arrays. Each actual vector rectangle demand is bounded by

   \[
   O(\ell^6K_1R)+O(\ell n)=o(K_2R).                       \tag{22}
   \]

   The first term is paid by the fixed 50-power gap between levels 1
   and 2. For the second term, its ratio is
   `O(ell^1001/R)`, which tends to zero by (18). Each level-2 rectangle
   realizes one recombined vector demand, preserving the already fixed
   horizontal directions. All axis targets are now exact.
4. **Bodies.** The old numerical supports avoided them, so their errors
   remain `O(H)`. Their level-3 cuboid reservoirs fix the four body sums,
   preserving every axis and the other bodies. Fresh reflection orbits
   keep the added drift on every face line at `O(R)`.
5. **Faces.** Their residual errors are `O(K2 R)` after the old line-load
   caps and the body correction. Each of the six families has exact
   total zero by the corresponding diagonal-square compatibility
   identity. Four-coordinate integral edge flows cost
   `O(kappa_G K2R)=o(K3R)`. The level-3 reservoirs fix each family
   while preserving all axes, all bodies, and the other five families.

This covers every `3n^2+6n+4` full signed-coordinate line and proves PC4.
The four coordinate flows never move separate coordinates of entries:
they compute a vector demand in `Gamma`, and Z4 decodes that demand
into one subset of actual whole-element swaps.

## 11. What this proves and what must be composed separately

PC4 is a complete conventional physical-transfer theorem under Inputs 1--3.
Its new rank-four obligations are paid by DG, PF, Z4, centered antipodal
endpoint boxes, and IT. In particular a vanishing conjugate mean does
not require changing the prescribed representative pool, and the old
cube rounding cost is explicitly replaced rather than ignored.

To conclude an eventual prime-array theorem one must compose PC4 with:

* the proved frozen normalization and local arithmetic, including the
  exact unit group, half-open boundaries, prime-ideal enumeration,
  centroid, and the eighth-root exceptional-associate exclusion;
* the analytic prime boxes used in Input 3, with all canonical-region
  hypotheses verified;
* compatible prime target tensors within `o(H)` of `mu`, with exact
  pool total `T`, including the six face-family totals for cubes.

The analytic target construction may use fixed three-form completion;
it must not apply a fixed-complexity theorem to a growing whole-array
system. Targets near a vanishing second embedding need their own
four-dimensional volume and norm audit. PC4 does not supply that audit.
Once those separate inputs are proved, its order classes are every
sufficiently large order for `m=5,12` and every sufficiently large odd
order for `m=8`. Necessity of the eighth-root oddness belongs to the
separately proved angular obstruction, not to PC4 itself.

All asymptotic ratios displayed here tend to zero on the complete
integer tail, with the field and exponents fixed. The analytic threshold
can remain ineffective. There is no evaluated cutoff, growing-conductor
uniformity, efficient implementation claim, or inference of asymptotic
truth from finite fixtures.
