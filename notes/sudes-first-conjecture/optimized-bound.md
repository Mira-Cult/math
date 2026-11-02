# An explicit classical cutoff of 2^4320

Public exposition of the optimized classical proof. Review and source provenance are recorded in [Provenance](PROVENANCE.md#optimized-bound).

## The complete odd-order tail

**Theorem.** For every odd integer


```math
\boxed{n\ge 2^{4320}},
```


there is an n-by-n square containing exactly the first n squared odd primes,
each once, for which every row sum, every column sum, and both main diagonal
sums are prime. These prime sums may repeat; they are not required to be equal.

The proof is unconditional and classical, using the explicitly identified
Rosser--Schoenfeld, Bennett--Martin--O'Bryant--Rechnitzer and McCurley
inputs. The scripts certify finite
inequalities and source integrity; the analytic imports, explicit-formula
derivation and finite construction remain conventional mathematical proofs.
No end-to-end kernel-checked theorem or enumerated square at this order is
claimed.

The [initial public bound](explicit-bound.md) remains preserved as a separate manuscript. Intermediate quantitative profiles are retained in the source history and recovery record. The new
proof below specializes the actual numerical hypotheses of the controller
and targets. It does not invoke an old theorem outside its literal domain.

## 1. Notation and exact active dependency graph

Keep the original definitions


```math
X=p_{n^2+1},\quad T=\sum_{j=2}^{n^2+1}p_j,\quad
 m=T/n^2,\quad y=T/n,\quad
 E=\lceil\log_2X\rceil,\quad e=\lceil\log_2y\rceil.
```


Here e is an integer parameter; analytic logarithms are natural logarithms.
The baseline design used `K=floor(n/E^3)` and `D=y/e^4`. The new design is


```math
K=\left\lfloor\frac n{1308}\right\rfloor,\qquad D=\frac y{1370},
 \quad\delta=\frac1{29092},\quad w=\frac3{28},\quad N_b=3117,
 \quad F_e=e(7+2\lceil\log_2e\rceil)^2.                \qquad\text{(CC1)}
```


| Producer | Output consumed by this composition |
|---|---|
| RS62, preserved M0, [coupled model](optimized/cutoff_coupled_model.md) CM | `n^2<=X<n^3`, `2X/5<m<3X/5`, `X/n^2>logX-3/2>Q(E)`, upper prime index, simultaneous ceiling bounds |
| [Constant analytic source](optimized/cutoff_constant_window_analytic.md), MR | `m<501X/1000` when `logX>=1000`, for exactly the odd-prime input pool |
| [Seed density refinement](optimized/cutoff_seed_density_refinement.md), SD | Even `2<=g<=159E/200`, reduced seed class, at least `floor(X/(2048E^3))` vertex-disjoint seed pairs |
| Corrected E2, N2, AL and [ZH0](optimized/cutoff_relaxed_height_analytic.md) | Signed exceptional contribution, primitive inducing-character normalization with omitted prime powers paid, parameterized zero-sum estimates in the stated domains |
| Constant analytic source, CW-macro | `logY>=5982`, even `q<=ceil(log2Y)`, centered intervals inside `[Y/2,2Y]`, length at least `500Y/6241273`, count at least `H/(2phi(q)log(2Y))` |
| Constant analytic source, CW-target | `logy>=8990`, radius `D=y/1370`, interval length at least `D/2`; weak moduli at most `.369e^2`, strong even moduli at most e |
| [Target construction](optimized/cutoff_target_optimization.md), TQ, and TD | Prime target lists with prescribed unit classes, exact total T and length n; selected modulus `h<=g ceil(.693148(e+1))` |
| [Degree-10 graph](optimized/cutoff_degree10_graph.md), G10 | Every order admits a graph of maximum degree 10 with cut expansion one half; multiplicities retained, loops discarded |
| [Constant controller](optimized/cutoff_constant_window_controller.md), CWC | Phase-specific prefix budgets, adaptive aggregate wide stocks, disjoint entry positions and diagonal rectangles, degree-specific centering, full integral correction capacity |
| This composition | Every source and finite hypothesis on the entire odd-order tail; all prime targets inside the controller correction box |

The original FC construction supplies the permutation and switch identities,
six-pass placement, concentration and integral-flow machinery. AFC, RBC
and CWC explicitly change the allocation and centering invoices. The new
master manifest includes every transitive source used by every replay,
including the historical certificates. The import manifest separately
records source locators, domains, provenance and the dependency edges.

## 2. Coupled order, index, ceiling and mean estimates

Write `v=log2 n>=4320`. The CM estimates, valid pointwise for every real v
in this range, give


```math
E\ge2v\ge8640>8192,\quad E\le4v,\quad n\ge E^{32},
 \quad 5E/4\le e\le2E,\quad E<(167/250)e.             \qquad\text{(CC2)}
```


The growth estimate follows from `2^v>=(4v)^32` at the base and the
increasing real ratio thereafter. Every floor or ceiling is bounded
pointwise; no derivative is applied to a rounded function. The stronger
index estimate retains a logarithmic gain that the original depletion
comparison discarded:


```math
\frac X{n^2}>\log X-\frac32>
 Q(E)=\frac{693E-2193}{1000}.                         \qquad\text{(CC3)}
```


Since `logX>=2v log2>1000`, MR improves the upper mean to
`m<501X/1000`. It uses the exact identity
`T=X(pi(X))-integral_2^X pi(t)dt-2`; the sign of the subtracted integral
is proved before dividing by the upper bound on `pi(X)-1`. The older lower
bound `m>2X/5` remains sufficient for all lower scales below.

Define the increasing real lower envelopes


```math
G_c(v)=2v\log2+\log\{c(2v\log2-3/2)\},\qquad
 F(v)=3v\log2+\log\{(2/5)(2v\log2-3/2)\}.            \qquad\text{(CC4)}
```


These follow from CC3 and apply to each requested scale separately. Exact
rational logarithm enclosures give:

| Actual scale | Lower bound for its natural logarithm at v=4320 | Required log | First sufficient integer v for this envelope |
|---|---:|---:|---:|
| Global half-pool center `X/2` | 5996.795887299322 | 5982 | 4310 |
| Lower residue center `m-X/4` | 5995.591914494996 | 5982 | 4311 |
| Upper residue center `m+X/4` | 5997.058251563790 | 5982 | 4310 |
| Smallest wide-bin center, greater than `3X/70` | 5994.339151526501 | 5982 | 4312 |
| Target mean y | 8990.968563766972 | 8990 | **4320** |

The controller and ceiling-coupling floors are 4096 in log2 order for the
selected sufficient envelopes; the elementary order-growth floor is 333.
The exact target-list size inequalities are automatic at the controller
floor. Thus the maximum of the separately translated conditions is 4320.
This is a maximum of sufficient estimates, not a lower bound for the problem.

## 3. Verify the actual progression requests

Every reflected band is inside `(1,X)`. For every narrow interval or bin
with center Y, CC1 and the two mean bounds give


```math
\frac3{70}X<Y<\eta X,\qquad
 \eta=\frac{501}{1000}+\frac14+\frac3{28}
      =\frac{6007}{7000}<1.                           \qquad\text{(CC5)}
```


Its length is `2X/29092`, its endpoints sum to `2Y`, and its half-width
is at most `Y/2`. In particular its actual relative length is at least


```math
\frac{2}{29092\eta}=\frac{500}{6241273}.             \qquad\text{(CC6)}
```


The upper center bound in CC5 is necessary in CC6; substituting a looser
relative length would unnecessarily raise the macro scale floor. As
`Y>X/32`, the local ceiling `ell_Y=ceil(log2Y)` satisfies
`E<=ell_Y+5`. Since `ell_Y>=20`, the actual seed gap obeys
`g<=.795E<=ell_Y`. CW-macro consequently applies to every reduced class
in every narrow interval and all 3117 bins, whatever gap and class SD chose.
It also applies to the global interval `(X/4,3X/4]` at its own center X/2.

For the target construction, put `L_t=ceil(.693148(e+1))`. TD retains the
strong initial prime count and uses the integer fact that the selected
positive gap h is a multiple of g. It proves `h<=g L_t`. The coupled
ceiling estimate gives


```math
h<\frac{4601289711}{12500000000}e^2
     +\frac{11239539711}{12500000000}e
   <\frac{369}{1000}e^2,\qquad e\ge1024.              \qquad\text{(CC7)}
```


Also `g<=e`, so CW-target's strong count supplies the initial target pair
and each diagonal target. All remaining requested moduli are the selected
h, which is even and has the reduced class required by TQ. Every requested
target interval is inside `[y-D,y+D]` and has length at least `D/2`.
Target values may repeat, so this selection consumes no input entries.

CW-target and CW-macro retain the signed exceptional-zero contribution.
The sharper smoothing coefficient 2 applies only to the adverse or absent
exceptional zero. The favorable class pays coefficient 4 and uses its larger
main increment. The proof checks both budgets before summing lifted classes.
Small moduli are lifted to `Q=q ceil(100000/q)`; the unit-class projection
and the absence of any omitted multiplier prime in these intervals are
proved. The primitive/imprimitive identity is unchanged, with the omitted
Euler-factor prime powers charged explicitly. None of these steps assumes
the nonexistence of an exceptional zero.

## 4. The complete finite controller invoice

Use the selected degree-10 graph and let


```math
M=\left\lfloor\frac X{4E^2}\right\rfloor,\quad
 H_c=\left\lfloor\frac X{29092E^2}\right\rfloor,\quad
 s=\left\lceil\frac{4X}{gM}\right\rceil,\quad
 P=s+\left\lceil\frac{32XE}{gM}\right\rceil\le160E^3.
```


The first-stage and total entry budgets are


```math
B_0=(20n+8)P+4(n+1)(g/2-1),\qquad
 B=B_0+(20n+8)7K.                                    \qquad\text{(CC8)}
```


All prefixes and residue repairs are reserved first, paying only B0 against
their class supplies. Their orientations remain selectable after the
baseline is known. Wide reservoirs are then extended using paired reflected
bins and **all** reduced classes. A deletion decreases the sum of the
matched minimum stocks by at most one, because bins and classes are
disjoint. This remains true under adaptive and adversarial choices; no
independence of overlapping supplies is assumed.

In each bin and class, CW-macro supplies at least
`W=X/(29092 phi(g) log(2X))` entries. With S the sum of the smaller
stock in every matched bin/class pair, the selected invoice proves


```math
\frac{\log(2X)B}{X}
 <0.107110942194074742946509
 <\frac3{28}-\frac1{100000},\qquad
 S\ge\frac X{100000E},\quad S^2>3117X.               \qquad\text{(CC9)}
```


The first comparison uses CC3 and retains the natural logarithm in W.
Cauchy--Schwarz then gives more than `X/g` candidate pairs, indexed by bin
and reduced class; there are at most `floor(X/g)` positive g-multiple
differences. A repeated difference gives two vertex-disjoint pairs. The
same adaptive invariant supplies ordinary and diagonal reservoirs after
every earlier reservation. The proof never shares entry positions.

Reflection keeps each chosen midpoint within `delta X` of m despite the
large total band width. The differences are between `2X/7` and `5X/7`;
seven stages per K still cover radius `2KX`, including the exact lower
endpoint equality. The prefix remains long enough to absorb the largest
wide difference.

The degree-10 graph has at most `5n` edges per network and cut expansion
one half. Its proof splits the small and large cut union bounds and obtains
`3/37+27/50=1149/1850<1` for every n at least eight; complete graphs
cover smaller n. Multiplicities are separate reservoirs. The exact
integral flow demand is at most
`floor(KX/(2g))=floor(floor(KX/g)/2)`, so this expansion suffices for
the entire zero-sum correction box.

The CWC certificate verifies the original seed count, prefix and residue
double-pair inequalities, floor losses, pool occupancy, all six embedding
passes, and joint placement of both diagonal rectangle families. It uses
the actual degree in the centering calculation:


```math
630\delta K+90P+10g+1+3\sqrt{n\log n}
 <\frac{2707}{125000}K.                              \qquad\text{(CC10)}
```


The certified left-side coefficient is less than
`0.021655437921077959576516`. This is the full midpoint, completion,
residue and concentration invoice. The conclusion is a baseline
permutation whose required line sums are reduced modulo g and within
`(2707/125000)KX` of y, together with the ability to realize all compatible
targets within `KX/2` of that baseline. Ordinary switches avoid both
diagonals. The two independent diagonal trades have disjoint supports and
preserve the row and column totals.

## 5. Exact prime target totals and final realization

For every integer `e>=256`, the dyadic-bin argument proves `F_e<=4e^2`,
including every jump of `ceil(log2e)`. From CC2,


```math
E^{28}>680\cdot16,\qquad
 \frac25 E^{92}>32768\cdot1370
```


imply the exact TQ requirements


```math
n\ge8e\{3F_e(4e+6)+7\},\qquad
 D\ge512F_e e^2,\qquad D\le y/4.                    \qquad\text{(CC11)}
```


The strict predecessor-gap condition in TD follows with ample integral
slack. The fine grid and wide-pair concatenation use bounded nonnegative
coefficient ranges; the two free CRT positions also handle shared prime
powers. Thus TQ produces a length-n row target list of total exactly T,
and independently a column list of total exactly T, in the required
classes. Both lie within D of y. The strong central count provides a prime
for each diagonal class. Its lower count exceeds one, so there is no
unverified endpoint existence assumption.

The floor in CC1 satisfies


```math
K\ge\frac{999999}{1000000}\frac n{1308},\qquad
 \frac D{KX}<\frac{7281200}{15222207},\qquad
 \frac{2707}{125000}+\frac{7281200}{15222207}
 <0.499983485627<\frac12.                            \qquad\text{(CC12)}
```


Every prime target is therefore strictly inside the full controller box.
The row and column totals agree exactly with T; both diagonal targets are
independent. Apply the integral corrections and diagonal trades. They
permute disjoint reserved entries and fill the remaining positions with the
remaining input primes, so every one of the first n squared odd primes
occurs exactly once. This proves the stated theorem for the complete odd
tail, with no subsequence restriction.

## 6. Whole-tail certification and limitations

The controller bounds use positive rational envelopes at `E>=8192`.
In particular V itself grows in the constant-K design; the proof instead
uses the decreasing quantities `V/E` and `(E+1)/Q(E)`. Every residual
prefix, placement and centering correction decreases. The lower scales
CC4 increase continuously. The analytic errors decrease as proved in CW;
source-domain ratios increase. Floor and ceiling changes are covered by
pointwise envelopes, exact integer inequalities or dyadic-bin induction.
An endpoint calculation alone is never used as a substitute for persistence.

The source campaign includes exact integer/rational arithmetic checkers, source-hash manifests, and negative tests. Those checkers certify the declared finite inequalities and source integrity, not the imported analytic results or the conventional construction. This public manuscript and its linked supporting proofs provide the mathematical argument without requiring access to the research repository. The separate executable recovery and precise review scope are described in [Provenance](PROVENANCE.md#optimized-bound).

[Manuscript index](README.md) · [Optimized theorem](optimized-bound.md) · [Source and review record](PROVENANCE.md#optimized-bound)
