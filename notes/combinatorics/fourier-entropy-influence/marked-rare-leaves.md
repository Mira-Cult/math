# Sharp constant four with arbitrarily many marked inputs

**Mira Cult · 16 November 2026**

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

Scientific source: [78ca8efe259785d4afdacd71f29b3d75cb85b537](https://github.com/Mira-Cult/math-wip/blob/78ca8efe259785d4afdacd71f29b3d75cb85b537/problems/0298-fourier-entropy-influence-conjecture/manuscripts/marked_set_rare_leaf_improvement.md).
The complete argument below has its own scoped nonauthor model review in
[Verification](VERIFICATION.md). This is not human peer review or formal
verification; general FEI remains unresolved.

The construction and its preserved signed-score invariant are proved in
[marked-set closure](marked-set-closure.md). This note proves the sharper
constant four for rare-point leaves, simultaneously over every allowed fixed
number of marks. All projection, branching and positivity hypotheses remain.

## 1. The improved theorem

For every integer `q>=2`, define a class as follows. Each leaf is

```math
r_n=1-2\mathbf1_x,\qquad n\ge2,
```

equipped with `q` distinct marked physical inputs, one of which is the
exceptional point `x`. Thus only leaves with `q<=2^n` may be used. At every
internal node take `m>=2+ceil(log_2q)` children on disjoint coordinate
blocks, form their product, and change its signs at the `q` concatenated
marked points. The projected marks are distinct in every child. The new
marked list is the concatenated list. The same `q` is used throughout a
finite construction; dimensions, arities and depth may vary without bound.

**Theorem.** Every Boolean function `f` so constructed has positive Fourier
spectrum and satisfies

```math
\boxed{H(f)\le4I(f).}
\qquad\text{(1)}
```

Here the cube is uniform, entropy is in bits, and
`I(f)=sum_S |S| fhat(S)^2`. The single constant four applies simultaneously
to every allowed integer `q`, not merely to each fixed `q` with a different
constant. For every fixed `q`, four is optimal, even if constructions are
required to contain an internal node.

The hypothesis that the exceptional leaf point is marked is part of this
theorem. Neither arbitrary positive Boolean leaves nor changes in the number
of marks within a construction are claimed. General FEI remains open.

## 2. The already proved closure invariant

We use Sections 2--6 of [the marked-set closure proof](marked-set-closure.md). For a marked positive Boolean
function `h` on `n` coordinates, let `delta=2^(1-n)`, and retain its
scores `P_h,K_h`, boundary imbalance `T_h`, and signed internal-edge sum
`E_h`. Set

```math
U_h=2P_h-4T_h,\qquad V_h=K_h-4E_h.
```

The source proves that the marked inequality

```math
4I(h)-H(h)\ge\delta\left[
\frac1{20}+\frac{|U_h|+2|V_h|}{4q^2-1}
\right]
\qquad\text{(2)}
```

survives every permitted internal node with the same constant four. This
closure is unconditional: positivity is preserved because the product's
nonzero Walsh numerators have absolute value at least `4q`; the exact
entropy/influence updates retain all cross terms and all shared edges; the
local score correction is at most `6q`; and the child-to-parent point-mass
ratio is at least `4q^2`. We do not repeat that proof. The new obligation is
to establish (2) at every rare-point leaf, uniformly in `q`.

## 3. Exact rare-point formulas, including adjacent marks

Reorder the marks so that the first is the exceptional point. Let `a` be
the number of marked ordinary points adjacent to that point, and let `b`
be the number of physical edges whose two endpoints are marked ordinary
points. Put

```math
\ell=\log_2\frac{1-\delta}{\delta}
       =\log_2(2^{n-1}-1).
```

The source's one-point scores are
`B_h(x)=-(2-delta)ell` at the exceptional point and
`B_h(y)=(2-3delta)ell` at each ordinary point. In the logarithm of the
Fourier law, only the empty spectral atom differs from the common value
of all the other atoms. Since the marked outputs are one minus sign and
`q-1` plus signs,

```math
\sum_{i\lt j}h(x_i)h(x_j)=\frac{(q-2)^2-q}{2}
=\frac{(q-1)(q-4)}2.
```

Substitution into the pair score and subtraction from the one-point sum
therefore give

```math
K_h=\delta(q-1)(q-4)\ell,\qquad
P_h=(q-2)(2-q\delta)\ell.
\qquad\text{(3)}
```

The sum of the individual point imbalances is `(q-2)n-2a`. The signed
internal-edge sum is `E_h=b-a`, so the exact boundary imbalance is

```math
E_h=b-a,\qquad T_h=(q-2)n-2b.
\qquad\text{(4)}
```

In particular the adjacent-to-exception edges cancel from `T_h`; the
ordinary-to-ordinary edges do not. Define the nonnegative scalar

```math
A=4(q-2)(n-\ell)+2q(q-2)\delta\ell.
\qquad\text{(5)}
```

Equations (3)--(4) now read

```math
U_h=8b-A,\qquad V_h=K_h+4a-4b.
\qquad\text{(6)}
```

For all `n>=2`,

```math
1\le n-\ell\le2,\qquad
0\le\delta\ell\le\delta(n-1)\le\frac12.
```

It follows that

```math
4(q-2)\le A\le(q-2)(q+8).
\qquad\text{(7)}
```

These bounds retain the cancellation of the apparently growing `n` terms
in `U_h`. Bounding the terms of `U_h` before that cancellation would lose
the result.

## 4. A uniform leaf-score bound

We prove

```math
\boxed{|U_h|+2|V_h|\le\frac45(4q^2-1)}
\qquad(q\ge2).
\qquad\text{(8)}
```

### 4.1. The case `q>=4`

Here `K_h>=0` and

```math
0\le K_h\le\frac{(q-1)(q-4)}2,\qquad 0\le a\le q-1.
\qquad\text{(9)}
```

For any three nonnegative real numbers `A,B,t`,

```math
|t-A|+|t-B|\le\max\{A+B,\,2t-A-B\}.
\qquad\text{(10)}
```

Indeed the left side is the maximum of
`A+B-2t`, `2t-A-B`, and `|A-B|`, and both the first and third
are at most `A+B`. Apply (10) with `t=8b` and `B=2K_h+8a`.
Using (6)--(9) gives

```math
|U_h|+2|V_h|
\le\max\left\{2q^2+9q-20,\;16b-4(q-2)\right\}.
\qquad\text{(11)}
```

The first term is at most the right side of (8): after multiplication
by five the difference is

```math
6q^2-45q+96=6(q-4)^2+3(q-4)+12\gt 0.
\qquad\text{(12)}
```

For `4<=q<=8`, bipartiteness of the cube gives
`b<=(q-1)^2/4`. Consequently the second term in (11) is at most
`4q^2-12q+12`. Its difference from the right side of (8), after
multiplication by five, is

```math
-4q^2+60q-64\ge28q-64\gt 0,
\qquad\text{(13)}
```

where `q<=8` was used in the inequality.

For `q>=9`, the usual induced-edge bound on the cube gives

```math
b\le\frac{(q-1)\log_2(q-1)}2\le\frac{q(q-1)}6.
\qquad\text{(14)}
```

For completeness, a set of `u` cube vertices spans at most
`u log_2 u/2` edges. Induct on the dimension, split the set into sizes
`u_0,u_1`, and bound the cross edges by `min(u_0,u_1)`. The resulting
inequality reduces to `h_2(t)>=2t` for `0<=t<=1/2`, which follows
from concavity between the endpoints. The second inequality in (14) uses
`log_2 u<=(u+1)/3` for integers `u>=8`. It is equality at eight, and
the increment from `u` to `u+1` is at most `log_2(9/8)<1/3`, because
`9^3<2*8^3`.

The second term in (11) is now at most
`(8/3)q^2-(20/3)q+8`. Its difference from the target in (8) is

```math
\frac{8q^2+100q-132}{15}\gt 0\qquad(q\ge9).
\qquad\text{(15)}
```

This proves (8) for every `q>=4`.

### 4.2. Three marks

When `q=3`, (7) gives `4<=A<=11`, and
`-1<=K_h=-2delta ell<=0`. There are two ordinary marked points,
so `b` is either zero or one. If `b=0`, then `a<=2`, and (6) yields

```math
|U_h|+2|V_h|\le11+16=27\lt 28=\frac45(4q^2-1).
```

If `b=1`, triangle-freeness of the cube forces `a<=1`. Thus
`|8b-A|<=4` and `|K_h+4a-4b|<=5`, giving a bound of fourteen,
which is even smaller. This includes every adjacency pattern of the
three marks.

### 4.3. Two marks

When `q=2`, `A=b=0`, `-1<=K_h<=0`, and `a` is zero or one.
Hence `U_h=0` and `|V_h|<=4`, so
`|U_h|+2|V_h|<=8<12=(4/5)(4q^2-1)`. This completes (8).

## 5. Entropy payment and conclusion

The entropy and influence of a rare-point leaf do not depend on its marks:

```math
I(h)=n\delta,\qquad
H(h)=-2(1-\delta)^2\log_2(1-\delta)
 +(2\delta-\delta^2)(2n-2).
```

As proved in Section 8 of [the marked-set closure proof](marked-set-closure.md), or directly from
`-ln(1-delta)<=delta/(1-delta)`,

```math
4I(h)-H(h)
\ge\left(4-\frac2{\ln2}\right)\delta
 +\left(2n-2+\frac2{\ln2}\right)\delta^2
\gt \delta.
\qquad\text{(16)}
```

The last strict inequality follows from `ln2>2/3`. By (8), the right
side required by the leaf invariant (2) is at most

```math
\delta\left(\frac1{20}+\frac45\right)
=\frac{17}{20}\delta\lt \delta.
\qquad\text{(17)}
```

Every leaf therefore satisfies (2), uniformly in `q`. The already
proved closure invariant and support argument apply at every node and
prove (1).

To prove optimality for a fixed `q`, rare-point leaves on `n` coordinates
have `H/I->4` as `n->infinity`, and admit the required `q` marks once
`2^n>=q`. For optimality with an internal node, fix any allowed arity
`m>=3`, take `m` such `n`-coordinate leaves, and modify their product
at its `q` parent marks. The product has influence `mn2^(1-n)` and
entropy `mH(r_n)`. Its influence changes by at most
`qmn2^(1-mn)`. The Fourier laws before and after modification have total
variation at most

```math
\|G-F\|_2=2\sqrt{q}\,2^{-mn/2}.
```

The entropy difference is at most `h_2(t)+tmn` for this total variation
`t`, by the elementary coupling entropy bound. Since `q,m` are fixed
and `m>=3`, both errors divided by `mn2^(1-n)` tend to zero. The
internal-node ratios therefore also tend to four. This argument proves
optimality separately for every fixed `q`, while the upper bound was
uniform simultaneously in all `q`.

## 6. Scope, verification, and remaining gap

This is a strict improvement of the earlier source's rare-point theorem:
its sharp constant four now covers arbitrary fixed marked-set size,
instead of two marks only. The source's separate generic-leaf theorem
remains `H<=(5C_0/4+7)I`; the present leaf proof uses the exceptional
point and does not improve that theorem for arbitrary leaf classes.

The result retains positivity and all projection-separation and arity
hypotheses. It does not claim a decomposition of an arbitrary Boolean
function into these nodes. Its `q=2` subfamily already includes the
positive spectra with full-dimensional logarithmic interaction from
Section 9 of [the marked-set closure proof](marked-set-closure.md). Necessary interaction size alone is not
a publication-priority certificate; the added mathematical content is the
leaf-score cancellation and uniform cost of all ordinary-mark edges.

The companion `check_marked_set_rare_leaf_improvement.py` uses exact
rational arithmetic for the universal polynomial checks and imports the
frozen marked-set checker's integer Walsh and rational logarithm routines
for its stated finite Boolean checks. These checks do not substitute for
the proofs above. The finite log calculations use certified intervals and
no floating-point tolerance.

Independent review should check (3)--(7), the direction of (10), all
three ranges in the proof of (8), the use of induced edges of ordinary
marks rather than all marked edges, and the quantifiers distinguishing a
fixed `q` within a construction from the single constant across all `q`.
The separate additive review is recorded in [VERIFICATION.md](VERIFICATION.md); review of the closure prerequisite alone would not cover the new leaf bound.
