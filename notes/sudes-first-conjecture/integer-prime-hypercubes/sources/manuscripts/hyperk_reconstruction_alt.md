**Public reading copy.** Presentation and links have been normalized. Historical status statements below belong to their source revisions; see the [current publication status](../../README.md#review-and-verification-status). The matching original bytes are in the [source archive](../../originals/manuscripts/hyperk_reconstruction_alt.md).

# A distributed integral absorber for every signed-line kernel

This is a new author component for the continuation of PR83. It preserves the frozen incidence, target, axis, half-family and local-selector sources. The manuscript-local result **AF(d)** supplies an exact integer finish with a polynomial coefficient bound. Its bound is suitable for a small residual; it is not by itself the required main controller for a residual comparable to the prime scale. Independent review must be attached to an exact revision before this component is called reviewed.

Definitions remain in [PROBLEM.md](../PROBLEM.md). Write `I={-m,...,m}`, `n=2m+1`, and let `K_d` be the integer kernel of all full signed-coordinate line contractions, including axes. We use PS and LP from [hyperk_kernel_research.md](hyperk_kernel_research.md), and eventual saturation IK from [hyperk_incidence.md](hyperk_incidence.md) only for the residue assertion.

## 1. The exact absorber statement

**AF(d).** Fix `d>=1`. There are finite constants `M_d,A_d,B_d,S_d,C_d` such that for every `m>=M_d` there is a fixed indexed family `Gamma_(d,n)`, independent of the input tensor, with the following properties.

1. Each template belongs to `K_d`, has entries in `{-1,0,1}`, support at most `S_d`, and a disjoint pairing of opposite-sign cells along any chosen coordinate.
2. There are at most `A_d n^d` indexed templates, and each cell lies in at most `B_d` of their supports. Index multiplicity is included.
3. Every `M in K_d` has an exact integer expansion `M=sum_G c_G G` with `max_G|c_G|<=C_d||M||_1<=C_d n^d||M||_infinity`.
4. For every integer `q>=1`, this same family generates the full incidence kernel over `Z/qZ`. Coefficients have representatives in `{0,...,q-1}`; no nonunit division is used.

For `d=0`, use the one empty tensor and its scalar coefficient. AF explicitly has an `n^d` multiplicative loss. A separate small-error production lemma is required before applying it at the prime scale.

Here are generous computable constants. For `b>=2`, let `a_b,s_b` be the alphabet and support invoices of PS(b), and put `a_1=s_1=1`, `h_b=a_b-1`. Thus

`a_b=b+1+sum_(c=2)^(b-1) binom(b,c)a_c`,

`s_b=sum_pi 2^(b-|union pi|) product_(C in pi)s_|C|`,

where `pi` ranges over disjoint proper unsigned blocks of size at least two. Set `t_0=0,u_0=1`; for `z>=1` put

`t_z=z+sum_(b=2)^z binom(z,b)2^(b-1)a_b`,

`u_z=sum_pi 2^(z-|union pi|) product_(H in pi)s_|H|`,

where the last sum is over all disjoint signed blocks of size at least two. Define

```
P_d = t_d + d max_(1<=b<=d) h_b,
H_d = 2d+1,
F_d = P_d+2d,
Delta_d = 2(F_d+1)+1,
S_d = (max_(0<=z<=d)u_z) (2 max_(1<=b<=d)s_b)^d,
T_d = sum_(Z subset [d]) sum_(pi partition of [d]\Z) 2^(d-|Z|-|pi|),
A_d = H_d T_d (1+Delta_d)^d,
B_d = H_d T_d (d Delta_d)^d,
C_d = 2 T_d (1+2S_d)^T_d,
M_d = max{H_d P_d+2d+2, 2^(d+1)d^2, 3^d}.
```

Include the empty partition in `T_d`; in particular `T_d<=(2d+1)^d`. The final term in `M_d` overpays the stable range of IK: it is a bound on the positive-orbit count, so certainly `n>=3^d`. No numerical efficiency is intended.

## 2. Generic axis cycles: an elementary integer contraction

A tensor on `(I\{0})^p` is **generic** when every support cell has distinct absolute coordinate labels. A generic box is

`R(a,b)=tensor_(i=1)^p(e_(a_i)-e_(b_i))`,

with distinct nonzero endpoints in every factor, and pairwise disjoint orbit sets `{|a_i|,|b_i|}` between different factors. Endpoints `a_i=-b_i` are allowed within one factor.

**GA(p).** If `m>=2^(p+1)p^2`, every generic integer zero-axis-margin tensor `F` is an integer combination of generic boxes with total absolute coefficient at most `2||F||_1`.

Choose distinct positive anchors `b_1,...,b_p` uniformly from the `m` orbit labels. Zero margins give the exact star identity

`F=sum_x F(x) tensor_i(e_(x_i)-e_(b_i))`.                 (A1)

On expansion, every term except the unchanged cell tensor contains a nonempty coordinate marginal and vanishes. Call `x` good when its orbit labels avoid all anchors. Its box is generic. Subtract the good boxes, leaving `F'`. Both the initial tensor and the subtracted boxes are generic zero-margin tensors, so `F'` is too. By (A1),

`||F'||_1<=2^p sum_(x bad)|F(x)|`.

For a fixed cell a union bound gives `Pr(x bad)<=p^2/m`. Hence some anchor tuple has

`||F'||_1<=(2^p p^2/m)||F||_1<=||F||_1/2`.

Choose it. The operation is integral. Iteration terminates because a nonzero integer tensor has positive integer `l1` norm. Total box coefficient cost is at most the geometric sum `2||F||_1`. This proves GA, with signed endpoints, without rational averaging or an external homology import. Exhaustive search would find an acceptable anchor tuple at each step.

## 3. Rooted pure selectors with common auxiliary coordinates

For a signed block `(B,sigma)`, normalize `sigma` at its first coordinate. Fix `h_|B|` private positive auxiliary orbits. For every nonzero `t` outside them construct `Q_(B,t)` as follows. For a singleton it is the point mass at `sigma_i t`. Otherwise begin with

`U_(B,t)=tensor_(i in B)(e_(sigma_i t)-e_(sigma_i b_i))`,

where the `b_i` are distinct private positive auxiliaries. For each proper `C subset B`, `|C|>=2`, choose a PS(C) selector on another private alphabet, reflected by the restricted signs. Use the same auxiliary selectors for every `t`. The PS formula gives

`Q_(B,t)=sum_pi (-1)^|pi| (tensor_(C in pi)Q_C)`
`             tensor (tensor_(i notin union pi)(e_(sigma_i t)-e_(sigma_i b_i)))`. (A2)

Here `pi` runs over disjoint proper unsigned blocks of `B`; restricted `sigma` supplies their signs up to simultaneous reversal.

The PS cancellation proof applies verbatim. Proper nonempty signed contractions vanish; the sole nonzero full-block contraction has signs `sigma` and value one. This holds for negative `t` as well: its absolute value avoids the auxiliary alphabet. The unique full-block diagonal support cell is `(sigma_i t)_(i in B)`, with coefficient one. There is no support on a different full-block signed diagonal. Every other support cell has at least two nonzero orbit labels in `B`. The singleton statement means simply that a point mass has total one.

Partition terms in (A2) have disjoint supports: their private auxiliary alphabets identify the selected proper blocks. Thus all entries are `+1` or `-1`.

For distinct nonzero `u,v` outside the auxiliaries set

`D_B(u,v)=Q_(B,u)-Q_(B,v)`.                              (A3)

This belongs to the full kernel on `B`, has entries in `{-1,0,1}`, and every surviving cell contains an endpoint `sigma_i u` or `sigma_i v` in some coordinate. Indeed, every cell using only auxiliaries is independent of `t` and cancels. The remaining supports for `u,v` are disjoint, also when `u=-v`. Support size is at most `2s_|B|`.

The endpoint property pays point load; fixed auxiliary data pay exact path telescoping. Unrelated pure selectors do not provide these two conclusions.

## 4. The center block

For a set `Z` of `z` coordinates apply LP(z) to `tensor_(i in Z)(e_0-e_(b_i))`, with distinct positive `b_i` and all projector selectors on disjoint private alphabets. Every signed block of size at least two has only the raw witness `t=0`, of coefficient one. The invoices are `t_z` auxiliary orbits and at most `u_z` cells.

The result `C_Z` lies in `K_z`, has entries `+1` or `-1`, and has coefficient one at the zero cell. Every other support cell has a nonzero auxiliary coordinate; no projector correction term contains the zero cell. For `z=1`, use `e_0-e_(b_1)`; for `z=0`, use the scalar one. This explicitly treats the odd-order center without a free-reflection assumption.

## 5. Signed equality strata and the finite triangular order

Every cell has a unique type `(Z,pi,sigma)`: `Z` is its zero-coordinate set; `pi` partitions the other coordinates into equal-absolute-value blocks; and a normalized sign vector records the relations inside each block. Its block parameter `t_B` is the first coordinate of `B`. Parameters are nonzero and have distinct absolute values. Let `p=|pi|`, the number of nonzero reflection orbits used by the cell.

**Stratum margin lemma.** If `M in K_d` vanishes on cells using fewer than `p` nonzero orbits, its restriction to a type with `p` blocks, expressed in the block parameters and extended by zero to nongeneric tuples, has zero axis margins.

Contract a block `B` while holding the other parameters fixed. Parameter zero or a signed copy of another block parameter yields a cell with fewer than `p` nonzero orbits, hence contributes zero. Every other summand belongs to the chosen type. The full `B`-line contraction is therefore exactly the asserted parameter margin. This integral argument includes both signs.

For a generic parameter box `R=product_B(e_(a_B)-e_(b_B))`, choose private auxiliaries disjoint from all endpoint orbits and form

`Lift_type(R)=C_Z tensor product_(B in pi)D_B(a_B,b_B)`.   (A4)

Factors are full kernel tensors on their coordinate blocks. A contraction crossing factors vanishes because their nonzero reflection-orbit alphabets are disjoint, and only the center factor uses zero. Thus (A4) lies in `K_d`, is `+1/-1` valued, and has support at most `S_d`.

On the chosen type it is exactly `R`. Every other surviving cell uses **strictly more than `p` nonzero orbits**. Each nonzero-block factor contains an endpoint outside its auxiliaries. A cell other than its full diagonal also uses an auxiliary orbit. A noncentral cell of the center factor adds an auxiliary orbit. Private alphabets make these new orbits distinct from those in the other factors.

Process types in increasing `p`, arbitrarily at a fixed `p`. The margin lemma and GA clear one type with compact lifts, preserving earlier types. For `p=0`, clear the single zero cell with a multiple of `C_[d]`; its cost still satisfies the loose bound `2||F_type||_1`. After `T_d` stages nothing remains.

Track `l1`, not the supremum norm. If the current norm is `L`, its type restriction has norm at most `L`. GA costs at most `2L`, and the compact lifts change the tensor by norm at most `2S_d L`. The next norm is at most `(1+2S_d)L`. Thus total compact-lift coefficient cost is at most `C_d||M||_1`. In particular no accumulated power `n^(1+2+...+d)` is introduced.

## 6. A fixed palette bank and an elementary robust graph

Take `H_d=2d+1` disjoint palettes, each of `P_d` positive orbits. For every type and palette fix the auxiliary data in Sections 3 and 4, assigning disjoint subpalettes to its factors. The invoice `P_d` suffices.

A generic parameter box uses at most `2p<=2d` endpoint orbits, so some palette avoids all endpoints. Use such a palette for its compact lift. Its rooted selectors retain the same auxiliary data while endpoints change.

Arrange positive orbit labels cyclically and join cyclic distances at most `F_d+1`. Put sign-preserving copies of these edges on the nonzero signed alphabet and join the two signs of each orbit. Maximum degree is at most `Delta_d`. Deleting at most `F_d` whole reflection orbits leaves a connected graph: successive surviving labels have cyclic gaps at most `F_d+1`, and sign-switch edges connect the copies. This requires no expander theorem. Long paths will not affect the maximum-coefficient bound.

Fix a deterministic simple path rule in every such deleted graph and orient graph edges once. For each type, palette, and generic tuple of graph edges avoiding that palette, include its lift (A4) in the indexed family `Gamma_(d,n)`.

Expand a compact lift by processing parameter factors in fixed block order. Join the first factor's endpoints by a simple graph path, deleting the palette and all other current parameter endpoint orbits. At most `P_d+2(p-1)<=F_d` orbits are deleted, and the two endpoints survive. Fixed auxiliary data give exact telescoping:

`D_B(u,v)=sum_(edges e along path) sign(e)D_B(e)`.

Each resulting parameter box is generic. Repeat for subsequent factors, now also forbidding the endpoints of already selected earlier graph edges. All final factors are graph edges, so the expansion uses the fixed indexed family.

**No maximum-coefficient loss.** Fix a final ordered edge tuple. Its first edge occurs at most once in the first simple path. That edge fixes the second path, which uses the second edge at most once. Continue inductively. Thus an indexed frame member occurs at most once, with sign `+1` or `-1`, in the expansion of one compact lift. Types and palettes are separate indices. After expanding all lifts, any one coefficient is bounded by their total absolute coefficient, at most `C_d||M||_1`.

This bounds a maximum coefficient. The total absolute coefficient after subdivision can be much larger and is not used. In particular the long paths are not inserted as a multiplier in the stratum ledger: telescoping leaves each original compact lift unchanged as a full tensor.

## 7. Point load, size, and physical pairing

Fix a type, palette, and output cell. In each nonzero block `B`, a surviving cell of `D_B(u,v)` exposes an endpoint outside the palette. Undoing the block sign in such a coordinate determines that endpoint. There are at most `|B|` coordinate choices and at most `Delta_d` incident graph edges. Hence at most `product_B(|B|Delta_d)<=(d Delta_d)^d` edge tuples can contain the cell. The central factor does not enlarge the count; with no nonzero blocks there is just one template for the palette. Summing over `H_d T_d` possibilities gives `B_d`.

The signed graph has at most `m Delta_d` edges. A type with `p` blocks contributes at most `(m Delta_d)^p` templates per palette, giving `A_d n^d` overall. These bounds count actual support, including support with zero net signed contraction.

Each template is `+1/-1` valued and has zero axis margins. In a fiber parallel to any chosen coordinate, positive and negative counts are equal. Pair them within the fiber. This partitions the support into opposite-sign pairs along that coordinate. Consequently the templates admit the grouped equal-gap prime-pair implementation required by the physical controller. Actual placement and prime supply remain separate dependencies; AF is a template and coefficient theorem.

## 8. Arbitrary residue rings

In the stable range IK says that the integer image of the full incidence matrix `A` is saturated. Let `Mbar` be in its kernel modulo `q` and lift it to an integer tensor `M0`. Then `A M0=q y` for an integer target vector `y`. Saturation gives `y=A Z` for an integer tensor `Z`, so `M0-q Z` is an integer kernel lift. Apply AF over the integers, reduce its coefficients modulo `q`, and take their least nonnegative representatives. There is no division inside the residue ring or assumption that `n` is invertible there.

This proves residue generation without asserting a small integer lift. No such bound is needed when a physical residue stage reserves `q-1` unit switches per fixed template.

## 9. Reproducibility and limits

[hyperk_reconstruction_alt.py](../../originals/code/hyperk_reconstruction_alt.py) checks rooted differences at positive, negative and opposite endpoints; complete signed signatures; central blocks; strict stratum spill; coordinate pairings; generic integer contraction; and fixed-palette telescoping. It retains the singleton-coordinate counterexample to a naive cellwise clearing order. Finite controls are not asymptotic proofs or prime-array certificates.

The result is the exact small-residual absorber AF. BK still needs an affordable approximation of a large compatible input, a sufficiently small integer residual, and the required physical load bounds. AF by itself has coefficient `O_d(n^d E)` for input norm `E`.


