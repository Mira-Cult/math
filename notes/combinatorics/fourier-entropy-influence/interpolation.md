# Physical interpolation with a half-bit query cost

**Mira Cult · 16 November 2026**

A physical restriction tree obeys an entropy–influence inequality with an
absolute cost of one half bit per expected query. The strict slack of
nonconstant Boolean forest leaves pays this cost for four fixed controls
and for first-hit decision lists of arbitrary length, even when every
payload uses the same data variables. The exact Fourier cross terms are
retained throughout; this is not a mixture identity for squared spectra.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

All inputs are uniform signs, all Fourier transforms are normalized, and all
entropy logarithms have base two. The influence of a coordinate is the
probability that flipping it changes the Boolean output. Write


```math
\mathcal D(f)=4I(f)-H(f).
```


The forest inputs are proved in [positive-forests.md](positive-forests.md)
and [deterministic-contractions.md](deterministic-contractions.md).

## 1. The interpolation theorem

Call a Boolean function an **admissible forest function** if its Fourier law
is full support and factors over a forest, or if deleting globally fixed
spectral coordinates and contracting deterministic equality/complement edges
gives such a law. Constants and characters are included. Genuine three-state support constraints are not included in this definition.

**Theorem 1 (restriction-tree interpolation).** Let a deterministic physical
restriction tree for a Boolean function `f` stop at Boolean functions `g_L`.
At each internal vertex it queries one as-yet-unfixed input coordinate; the
remaining data variables may be shared by arbitrarily many leaves. Let `D`
be its number of queries on a uniform input. Then


**Equation (1).**

```math
\boxed{\quad H(f)-4I(f)
 \le \mathbb E_L[H(g_L)-4I(g_L)]+
               \tfrac12\mathbb E D.\quad}
```


In particular, if every leaf is an admissible forest function, and `P` is
the probability of reaching a nonconstant leaf, then


**Equation (2).**

```math
\boxed{\quad H(f)\le4I(f)+\tfrac12\mathbb E D-2P.\quad}
```


Consequently `E D <= 4P` implies `H(f)<=4I(f)`. For constant `f`,
`H(f)=I(f)=0`; (1)--(2) remain valid, although a redundant restriction tree
can have `E D>0`.

**Corollary 2 (four controls).** If fixing four specified physical input bits
always leaves a nonconstant admissible forest function, then `H(f)<=4I(f)`.
The same holds with fewer than four controls. All branches may use all the
same remaining variables, and no orthogonality or disagreement lower bound
is assumed.

**Corollary 3 (arbitrarily long forest decision lists).** Let `z_1,...,z_k`
be fresh uniform controls, and let `g_1,...,g_{k+1}` be arbitrary nonconstant
admissible forest functions on one common data cube. Define `f(z,y)=g_j(y)`
at the first `j` with `z_j=+1`, and use `g_{k+1}` if no such `j` exists.
For every `k>=1`,


**Equation (3).**

```math
H(f)\le4I(f)-1-2^{-k}.
```


Indeed the first-hit restriction tree has
`E D=sum_{j=0}^{k-1}2^{-j}=2-2^(1-k)` and `P=1`. Thus neither the number of
controls, the number of branches, the ambient dimension, the Fourier degree,
nor the branches' overlap affects the constant four. The empty-list case
is the original forest theorem. Mixed constant leaves are covered by (2)
when its displayed budget holds; they are not silently covered by (3).

## 2. Exact interpolation and its information cost

For Boolean `g,h` on the same data cube put


```math
F(x,y)=\frac{1+x}{2}g(y)+\frac{1-x}{2}h(y),\qquad
 a_T=\widehat g(T),\quad b_T=\widehat h(T).
```


The Fourier coefficients are


**Equation (4).**

```math
\widehat F(0,T)=\frac{a_T+b_T}{2},\qquad
 \widehat F(1,T)=\frac{a_T-b_T}{2}.
```


These are amplitude sums. In particular `p_F` is not the half-and-half
mixture of the branch Fourier laws. The cross terms `+a_T b_T/2` and
`-a_T b_T/2` disappear only after the selector Fourier bit is marginalized.

Let `R_T=(a_T^2+b_T^2)/2`. It is both that marginal law and the law obtained
by first choosing a uniform physical label `J` and then sampling the Fourier
law of its branch. If `U` is the selector Fourier bit in `p_F`, the entropy
chain rule gives the exact identity


**Equation (5).**

```math
H(F)-\tfrac12[H(g)+H(h)]=H(U\mid T)+I(T;J).
```


This is the one-bit case of Shmalo's Proposition 8.6, credited below. The
mutual information and the conditional entropy are different terms. A cheap
physical label is not itself a proof that either term is paid by influence.

For a zero-mass pair `R_T=0` omit the term. Otherwise set


```math
t_T=\frac{(a_T-b_T)^2}{2(a_T^2+b_T^2)},\qquad
 d(t)=h_2(t)+1-h_2\!\left(\tfrac12+\sqrt{t(1-t)}\right).
```


The symmetry of binary entropy removes the sign of the square root. Direct
substitution in (4), or (5), gives


**Equation (6).**

```math
\Delta_x(F):=H(F)-\tfrac12[H(g)+H(h)]
       =\sum_T R_Td(t_T),\qquad
 I_x(F)=\sum_T R_Tt_T.
```


The two branch norms are one, so `sum_T R_T=1`. The following scalar bound
therefore charges all amplitude interference and all label information:

**Lemma 4.** For `0<=t<=1`,


**Equation (7).**

```math
d(t)\le4t+\tfrac12.
```


Equations (6)--(7) imply


**Equation (8).**

```math
\Delta_x(F)\le4I_x(F)+\tfrac12.
```


This is an absolute defect bound, not the false assertion
`Delta_x<=C I_x` for every coordinate. As `t` tends to zero, `d(t)/t`
diverges logarithmically. The half-bit defect in (8) is paid in Theorem 1
by the independently established forest slack at the leaves.

## 3. Complete scalar proof, with a rational certificate

The symmetry `d(t)=d(1-t)` reduces (7) to `0<=t<=1/2`.
Put `w=4t(1-t)`, so `0<=w<=1`. The binary entropy series is


**Equation (9).**

```math
1-h_2((1+z)/2)
   =\frac1{\ln2}\sum_{j\ge1}
          \frac{z^{2j}}{2j(2j-1)},\qquad |z|\le1.
```


Its coefficients are nonnegative and sum to one after division by `ln2`.
Keep the first two terms and bound every remaining `w^j` by `w^3`:


**Equation (10).**

```math
1-h_2\!\left(\tfrac12+\sqrt{t(1-t)}\right)
 \le\frac{w}{2\ln2}+\frac{w^2}{12\ln2}
       +\left(1-\frac7{12\ln2}\right)w^3.
```


The remainder coefficient is nonnegative, since it is a sum of positive
terms in (9). Also
`h_2''(t)=-1/[ln2*t*(1-t)]<=-4/ln2`. Integrating this bound about `t=1/4`
gives, with `L=log_2 3`,


**Equation (11).**

```math
h_2(t)\le2-L+Lt-\frac2{\ln2}(t-\tfrac14)^2.
```


The endpoints follow by continuity. We use only the rational bounds


```math
\frac{69}{100}\lt \ln2\lt \frac7{10},\qquad L>\frac{19}{12}.
```


For the first bounds the series for `ln2` gives
`56/81<ln2<25/36`; for the second, `3^12=531441>524288=2^19`.
In (11), the coefficient of `L` is `t-1<=0`. In (10), all powers of `w`
are nonnegative. Consequently (10)--(11) imply


```math
d(t)-4t\le P(t),
```


where


```math
P(t)=\frac5{12}-\frac{29}{12}t
       -\frac{20}{7}(t-\tfrac14)^2
       +\frac{50}{69}w+\frac{25}{207}w^2+\frac16w^3.
```


It remains a rational polynomial assertion. Set `Q(t)=1/2-P(t)`. Its power
coefficients, in ascending order, are


```math
(11/42,-3691/1932,5540/1449,-1408/207,6224/207,-32,32/3).
```


For clarity, the following table supplies the entire certificate. On an
interval `[a,b]`, write `u=(t-a)/(b-a)` and
`Q(t)=sum_{j=0}^6 B_j binom(6,j)u^j(1-u)^(6-j)`.
The entries below are `2782080 B_j`:

| interval | j=0 | j=1 | j=2 | j=3 | j=4 | j=5 | j=6 |
|---|---:|---:|---:|---:|---:|---:|---:|
| [0,1/4] | 728640 | 507180 | 330040 | 182436 | 71368 | 11130 | 16065 |
| [1/4,1/2] | 16065 | 21000 | 91108 | 240732 | 484264 | 828900 | 1274640 |

All entries are positive; the Bernstein basis is nonnegative and sums to
one on each interval. Thus `Q>0` there. This proves (7) on the first half.
If `t>=1/2`, apply the first half to `1-t` and use `4(1-t)<=4t`.
There is no numerical maximization in this proof. The companion checker
reconstructs every coefficient using exact rational arithmetic. ∎

## 4. Forest slack and adaptive telescoping

**Lemma 5 (forest slack, extracted from the reviewed theorem).** Every
nonconstant admissible forest function satisfies `D(g)>=2`.

For a nonuniform full-support law this is the stronger reviewed forest
theorem. For a uniform full-support quotient on `r>0` bits, the law has
entropy `r` and influence `r/2`. Since a Boolean Walsh coefficient is
rational, the common magnitude `2^(-r/2)` forces `r` even. Thus `r>=2`
and `4I-H=r>=2`. Fixed spectral coordinates and the deterministic contraction
preserve entropy and do not increase the quotient influence, so the same
slack holds before contraction. A quotient with no free bits means that the
original Boolean function is a character. A nonconstant character has
entropy zero and influence at least one. Constants have `D=0`. ∎

At an internal vertex `v`, let `f_v` be the current Boolean restriction and
let its queried coordinate be `i(v)`. The exact influence identity gives


```math
I(f_v)=I_{i(v)}(f_v)+\tfrac12[I(f_{v,+})+I(f_{v,-})].
```


Combine this with (8), multiply by the probability `p_v` of reaching `v`,
and sum. The child entropy and influence terms cancel against their parent
terms, including adaptive choices of the next coordinate. The leaf terms
are weighted by their true reach probabilities. Finally
`sum_{v internal}p_v=E D`. This proves (1), and Lemma 5 proves (2).

## 5. An infinite family outside every spectral forest

Let `A,B` each be binary vectors of length `2m`, `m>=1`, and put


```math
g(A,B)=(-1)^{\sum_{j=1}^m A_{2j-1}A_{2j}},\qquad
 h(A,B)=(-1)^{A\cdot B}.
```


The first function ignores `B`; it is bent on `A`. The second is bent on
`(A,B)`. Thus their Fourier laws are admissible forests (flat product laws
after deletion of fixed zero coordinates), and both are nonconstant. Their
one-bit selector `F_m` is covered by Theorem 1.

Write `r=2^m` and `N=r^2`. For a Fourier pair `(U,V)`,


```math
\widehat g(U,V)=\mathbf1_{V=0}\,2^{-m}\epsilon_U,
 \quad\epsilon_U=(-1)^{\sum_j U_{2j-1}U_{2j}},\qquad
 \widehat h(U,V)=2^{-2m}(-1)^{U\cdot V}.
```


Equation (4) therefore shows that `F_m` has **full spectral support**, with
the following magnitudes and multiplicities:

| magnitude | multiplicity |
|---|---:|
| `(r+1)/2^(2m+1)` | N |
| `(r-1)/2^(2m+1)` | N |
| `1/2^(2m+1)` | 2N(N-1) |

At `m=1` the last two magnitudes coincide; the table counts their sources
separately. The magnitude ratio is `2^m+1`, and hence is unbounded.
The numerator `r+1` is an odd integer greater than one. The reviewed
Boolean forest arithmetic theorem says that every nonzero Walsh magnitude
of a Boolean forest law is a power of two, even allowing zeros. Thus
**no forest factorization of the Fourier law of `F_m` exists**.

The family is not plateaued. It also cannot have the repository's
integer-flat-packet decomposition: such a decomposition of a Boolean
function consists of ternary signed physical packets, and a nonzero flat
ternary packet has a power-of-two Fourier magnitude. The odd numerator
above excludes that possibility. The bounded-spread theorem by itself has
constant `4(2^m+1)^2`, whereas Theorem 1 gives constant four uniformly.

For reproducible checks, exact Parseval summation gives


```math
I(F_m)=\frac{3m}{2}+\frac12-\frac1{2N},
```


```math
H(F_m)=4m+2-
 \frac{(r+1)^2\log_2(r+1)+(r-1)^2\log_2(r-1)}{2r^2}.
```


The common data are genuinely shared: `E[gh]=2^(-2m)`, not zero, so this
family does not satisfy neighboring-branch orthogonality. The weaker
positive-selector-influence result of Shmalo does apply to this particular
family with a coarser constant; the new statement is not claimed to be the
first dimension-independent estimate for this example.

There is also a version with arbitrarily many essential controls. Alternate
the two functions `g,h` down a first-hit decision list and use the opposite
of the last selected branch as its fallback. Every control is relevant.
For `k=2s>=4`, the coefficient of `h` in the physical selector average is
`(4^s-1)/(3*4^s)`, whose reduced numerator is an odd integer greater than
one. For `k=2s+1>=3`, it is `(2*4^s+1)/(3*2*4^s)`, again with odd numerator
greater than one. At a data Fourier set with `V!=0`, the zero-control
coefficient therefore has a nontrivial odd Walsh factor. These decision
lists also have no spectral forest factorization, and (3) applies for
every length. Taking `m` to grow as well avoids a bounded-data-dimension
specialization.

## 6. A sharper influence-only step when amplitudes are separated

For an auxiliary bridge, suppose at every data Fourier index the two
nonzero magnitudes `|a_T|,|b_T|` are either equal or differ by a factor at
least two. This holds whenever both branch spectra have only
power-of-two magnitudes. Then


**Equation (12).**

```math
\Delta_x(F)\le C_* I_x(F),\qquad
 C_*=36-18\log_2 3\quad(7.470\lt C_*\lt 7.471).
```


Here is the full scalar proof. Let `D(a,b)` denote the local raw-entropy
drop from (4). Its value depends only on the two absolute magnitudes, while
`(a-b)^2` is smallest when their signs agree. Homogeneity and interchange
therefore reduce an unequal nonzero pair to `a=1`, `b=t` with `0<t<=1/2`.
In natural-log units its drop is


```math
L(t)=(1+t^2)\ln2
 -\tfrac12[(1+t)^2\ln(1+t)+(1-t)^2\ln(1-t)]
 +t^2\ln t.
```


The derivative of `4L(t)/(1-t)^2` has the sign of


```math
(1+t)\ln\frac2{1+t}+t\ln t.
```


This expression decreases to zero at `t=1`, since its derivative is
`ln[2t/(1+t)]<0` for `0<t<1`. Thus the ratio increases on `[0,1/2]`.
Its endpoint value in bits is exactly `C_*`. Equal magnitudes have zero
drop, and a zero magnitude gives ratio four. This proves (12), including
all zeros. The scalar constant is attained at magnitude ratio two, though
no claim of sharpness for the Boolean class is made.

Consequently, if both separated-spectrum branches satisfy ordinary FEI
with constant `K`, then their selector satisfies it with constant
`max{K,C_*}`. For forest branches the slack argument is stronger and gives
four. This coefficient separation cannot be propagated through arbitrary
selectors: the new magnitudes contain odd sums such as `2^m+1`.

## 7. What failed, what is retained, and what remains open

An unrestricted convex mixture of Boolean Fourier laws has no useful
automatic information bound: the parity decomposition has label exactly
equal to the spectral sample. At the function level a convex combination
of sign functions can equal a sign function only when all positive-weight
summands agree at that input. A physical selector is therefore a different
operation; (4)--(6) account for its interference explicitly.

The successful repair is an absolute information defect paid from leaf
slack. It gives (1), rather than identifying `p_F` with a forest mixture.
The half-bit cost is paid once per actually reached restriction vertex,
which is why the unbounded first-hit lists remain dimension free.

The leaf slack is not automatically inherited with its original value.
For example, a selector between the constant one function and the two-bit
sign-AND produces three-bit sign-AND. The child has `D=2`, whereas the
parent has `D=3-H(AND_3)<2`. Thus repeated gluing without the explicit
depth/leaf budget would be invalid.

There is an explicit counterexample to dropping that budget altogether.
On four binary input bits let `b` be positive precisely at the integer
indices `{0,1,2,3,4,5,8,10}`. Its exact Walsh vector, in increasing binary
index order, is

```
[0,4,4,0,8,4,-4,0,8,-4,4,0,0,-4,-4,0].
```

It is balanced and has `H(b)=3`, `I(b)=3/2`. Define `b_d` by balanced
disjoint self-composition to depth `d`, with `b_1=b`. The established
balanced composition identities give


**Equation (13).**

```math
I(b_d)=(3/2)^d,\qquad H(b_d)=6((3/2)^d-1).
```


All nonzero Fourier magnitudes remain powers of two: balanced composition
has no constant child coefficients, so each nonzero output coefficient is
one product of gate and child coefficients. At `d=3`, `H/I=38/9>4`, and
the ratios tend to six. Thus even power-of-two magnitudes alone do not
extend the constant-four theorem to arbitrary Boolean spectra.

More directly, put `F(z,y)=b_4(z)y`. Every physical-control section is the
nonconstant forest character `+y` or `-y`, yet


```math
H(F)=195/8,\qquad I(F)=97/16,\qquad H(F)-4I(F)=1/8>0.
```


This explicit 257-input function refutes a constant-four closure theorem
for unrestricted forest selectors. It does not refute FEI with a larger
universal constant. The gate and the standard composition mechanism are
used as reproducible controls; no priority claim for this lower bound is
made, and stronger published lower bounds above six are already known.

Nor does allowing arbitrarily many uniform controls for free prove a
broader theorem: with `g_z(y)=b(z)\chi_A(y)`, every branch is a nonconstant
character, while `F(z,y)=b(z)\chi_A(y)` contains an arbitrary Boolean
function `b`. Then `H(F)=H(b)` and `I(F)=I(b)+|A|`. Tensor powers show
that a universal dimension-independent estimate for all such selectors
would already imply general FEI with the same asymptotic constant.

The remaining general obligation is to replace the absolute query defect
in (1) by a cost controlled by actual influence or by a sufficiently large
Boolean leaf deficit for an appropriate decomposition. Neither a general
low-information forest mixture nor this stronger restriction payment has
been proved here.

## 8. Literature, dependencies, and verification boundary

- Y. Shmalo, *Fourier entropy of threshold functions and their compositions*,
  [arXiv:2610.16069v1](https://arxiv.org/html/2610.16069v1), Proposition 8.6
  gives (5) and its multibit version, including the bound
  `H(F)<=2k+E H(g_z)`. Corollary 8.7 obtains constant FEI from neighboring
  branch orthogonality, or `I_sel>=c k`. Those statements do not require
  disjoint data, and are not new here. The present theorem instead pays a
  smaller influence-corrected defect using the forest theorem's strict
  slack and expected query depth; no such lower bound on `I_sel` is used.
  The older `+2` cost per visited query, combined with the reviewed leaf
  slack, already gives `H<=4I+2` for the first-hit lists above. A positive
  lower bound on the influence of their nonconstant forest leaves turns
  that into a coarser dimension-independent constant. Thus the advance is
  the preserved constant four and the explicit half-bit defect, rather
  than a claim that no constant FEI bound for this class was previously
  derivable from those ingredients.
- Gangopadhyay--Stănică, *The Fourier Entropy-Influence conjecture holds for
  a log-density 1 class of cryptographic Boolean functions*,
  [ePrint 2014/054](https://eprint.iacr.org/2014/054.pdf), Section 4.2,
  Theorem 8, treats concatenation with disjoint Fourier spectra. Its exact
  theorem hypothesis was recovered from the primary indexed PDF text;
  the full direct PDF was unavailable in the recorded source comparison. Our branches can overlap
  on every nonzero Fourier index.
- O'Donnell--Tan, [arXiv:1304.1347v1](https://arxiv.org/abs/1304.1347v1),
  Theorem 1, is a disjoint-input composition result with biased-spectrum
  hypotheses. Shared payload variables prevent a direct application of
  that theorem to the selectors here. Ordinary disjoint products of our
  new class inherit FEI by the established entropy and influence identities.
- Potapov's plateaued theorem, [arXiv:2609.21563v1](https://arxiv.org/abs/2609.21563v1),
  and the [integer-flat-packet and bounded-spread bounds](integer-flat-packets.md)
  have the stated intersections and exclusions in Section 5. No exhaustive
  publication-priority claim is made.

[code/check_forest_selector_interpolation.py](code/check_forest_selector_interpolation.py) reconstructs the polynomial
certificate exactly, checks all eligible pairs of Boolean functions through
three data bits with rational entropy enclosures, and verifies the displayed
bent selectors, alternating lists, and the displayed four-bit gate by exact
integer Walsh transforms. It verifies the depth-four counterexample's
entropy and influence by the exact proved composition recurrences.
Finite checks support the implementation and examples; the universal class theorem is established by the proofs above.
The exact independent-review scope is recorded in [VERIFICATION.md](VERIFICATION.md).
