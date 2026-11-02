# Sharper density in the seed interval and the selected target modulus

All analytic logarithms are natural. The coefficient


```math
b=\frac{693148}{10^6}
```


is a rational upper bound for `log 2`, not Euler's number or an integer
dyadic parameter. The accompanying program bounds `log 2` by its positive
atanh series and proves


```math
\frac{6931}{10000}\lt \log 2\lt b\lt \frac7{10},
 \qquad \log4\lt \frac75.                         \qquad\text{(SD0)}
```


## SD: a seed gap at most 159E/200

Let `X` be an integer and `E=ceil(log2 X)>=4096`. Then there are an
even gap


```math
2\le g\le\frac{159}{200}E                         \qquad\text{(SD1)}
```


and a reduced class `a mod g` with at least


```math
\left\lfloor\frac{X}{2048E^3}\right\rfloor
```


vertex-disjoint prime pairs `(p,p+g)` in `(X/4,3X/4]`, all lower
endpoints congruent to `a mod g`. The same old controller seed invoice is
preserved; this theorem trades some unused seed supply for a smaller gap.

### Density without the old 7/8 denominator padding

The primary input is RS62 (3.5)--(3.6), as recorded and expanded in E1 of
[effective_pair_supply.md](../classical-primes.md):
`pi(t)>t/log t` for `t>=17` and
`pi(t)<1.25506 t/log t` for `t>1`. These imported estimates are not proved
by the arithmetic checker. The primary source is the
[RS62 scan](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf),
printed p.69, Corollary 1.

Put `E_0=4096` and `t=log X`. Since `t>(E-1)log 2`, (SD0) gives


```math
\frac{\log(X/4)}{\log X}
 \gt r_0:=1-\frac{7/5}{(6931/10000)(E_0-1)}
 =\frac{810527}{810927}\gt 0.                         \qquad\text{(SD2)}
```


Every source threshold holds on this domain. Applying RS62 at the two
endpoints, and using `log(3X/4)<t<=bE`, proves that the number `M` of
primes in `(X/4,3X/4]` satisfies


```math
M\gt \left(\frac34-\frac{62753}{200000r_0}\right)
       \frac Xt
 \gt \rho_0\frac XE,
 \qquad
 \rho_0=\frac{353454739845}{561815168996}
 \gt 0.62912993338475.                                  \qquad\text{(SD3)}
```


The first lower bound remains valid for every larger integer `E` because
the denominator ratio in (SD2) increases. The second uses a fixed
rational lower coefficient, so no rounded parameter is differentiated.

### Screen, match, and count the actual possible labels

Write `lambda=159/200`. List the `M` primes in increasing order and
consider every consecutive edge. Their gap sum is strictly less than
`X/2`. Fewer than `X/(2lambda E)` edges have gap greater than
`lambda E`. Thus more than


```math
\left(\rho_0-\frac1{2\lambda}\right)\frac XE-1
```


short edges remain. They form a disjoint union of paths. Taking alternate
edges in each path produces a vertex-disjoint matching of size greater
than


```math
\frac12\left(\rho_0-\frac1{2\lambda}\right)
       \frac XE-\frac12.                            \qquad\text{(SD4)}
```


Each gap is even. Each lower endpoint is a prime greater than
`X/4>E>=g`, so its residue is reduced. With
`j=floor(lambda E/2)`, the number of possible gap/residue labels is at
most


```math
j(j+1)\le\frac{\lambda E(\lambda E+2)}4.             \qquad\text{(SD5)}
```


The linear `+2` term is retained. Subtracting the matching size needed
to supply `X/(2048E^3)` per possible label leaves a coefficient at
least


```math
\begin{split}
 \eta_0&=
 \frac12\left(\rho_0-\frac1{2\lambda}\right)
 -\frac{\lambda(\lambda+2/E_0)}{8192}\\
 &=\frac{41886407253843599599}
 {1873356770411576033280000}
 \gt 0.000022359.                                       \qquad\text{(SD6)}
\end{split}
```


For all integer `E>=32`, `2^(E-1)/E` is increasing, and


```math
\frac XE\gt \frac{2^{E-1}}E\ge\frac{2^{31}}{32}=2^{26}.
```


The exact check `eta_0*2^26>1/2` therefore pays the subtraction in
(SD4), with substantial room. The matching has more than
`lambda E(lambda E+2)X/(8192E^3)` members. By (SD5), at least one
label has more than `X/(2048E^3)` members, proving the stated weaker
floor bound. The matching precedes pigeonholing, so all retained pairs
remain vertex-disjoint. When `X=p_(n^2+1)`, every endpoint lies in the
exact first-`n^2` odd-prime input pool.

## TD: use the actual rational upper bound for log 2 in target selection

Keep all the finite and congruence hypotheses of TQ, including
`ell=ceil(log2 y)>=3`, even `g<=16ell`, `F>=ell`,
`D>=512Fell^2`, `D<=y/4`, and its stated list-length requirement.
Assume the strong count


```math
\frac{|I|}{2\varphi(g)\log(2y)}
```


on each required interval of length at least `D/2` inside
`[y-D,y+D]`. Put


```math
L_b=\left\lceil b(\ell+1)\right\rceil.              \qquad\text{(TD1)}
```


The repeatable target-prime difference can be chosen as a positive
multiple `h` of `g` satisfying


```math
h\le gL_b.                                           \qquad\text{(TD2)}
```


To prove this directly, `L_b<=ell` for integer `ell>=3`, and
`2phi(g)log(2y)<g b(ell+1)<=gL_b`. The central interval of length
`D/2` therefore has at least `M_0>=D/(2gL_b)` primes in the chosen
class. The size condition implies


```math
D\ge512\ell^3\gt 32\ell^2(\ell+1)
       \ge2gL_b(L_b+1).                              \qquad\text{(TD3)}
```


There are at least two such primes, and their smallest consecutive gap
is at most `D/[2(M_0-1)]<g(L_b+1)`. This positive gap is a multiple
of `g`, so it is at most `gL_b`. This argument handles real `D` and
nonintegral lower bounds for `M_0`; the actual number of primes is an
integer at least that lower bound.

Reapply Steps 2--6 of TQ with this smaller chosen `h`. Their grid, wide
pairs, two-coordinate congruence lift, and exact-total balancing arguments
are unchanged. The weak supply is only needed at this selected modulus,
with density `|I|/(hF)`, on the same length-`D/2` windows. Repeating
target prime values is permitted by TQ; repeating input entries is not
introduced. This is a new application of the seed argument, not an
invocation of a theorem whose original larger weak-modulus premise has
been silently removed.

## A useful explicit composition cap

Suppose a square composition independently proves


```math
E\lt \frac{167}{250}e,\qquad e\ge1024,
```


and uses SD and TD with `ell=e`. Then


```math
\begin{split}
 h&\le gL_b
 \lt \frac{159}{200}\frac{167}{250}e
       \bigl(be+b+1\bigr)\\
 &=\frac{4601289711}{12500000000}e^2
   +\frac{11239539711}{12500000000}e
 \lt \boxed{\frac{369}{1000}e^2}.                       \qquad\text{(TD4)}
\end{split}
```


The last strict inequality is checked exactly at `e=1024`, after which
the linear coefficient divided by `e` decreases. The coupling
`E<(167/250)e` and the required square-order scale are separate
composition obligations; this manuscript does not assume them from
unrelated worst cases. A still tighter cap is numerically possible, but
the clean rational (TD4) is the result proposed here.

## Exact checks and limits

Executable replay details are recorded in [Provenance](../PROVENANCE.md#optimized-bound).

The checker contains the complete rational parameter set and strict
dependency map. It checks the logarithm series bounds, fixed density,
matching and label margin, integer-bin persistence, target gap coefficient,
and the conditional cap (TD4). It rejects missing, empty, malformed,
mismatched, or extra dependency records and tests deliberately insufficient
gap and cap choices. Finite controls exercise the exact gap-label floor
and the target ceiling; they support these formulas but do not replace
the proofs for arbitrary integers.

RS62, its prime-density consequences, the finite target construction,
strong and weak analytic supplies, and the square controller remain
mathematical inputs. This program does not prove those imports, construct
an actual square, verify a zero list, or assert a complete all-odd cutoff.
The earlier seed and target sources remain separately reproducible.

[Manuscript index](../README.md) · [Optimized theorem](../optimized-bound.md) · [Source and review record](../PROVENANCE.md#optimized-bound)
