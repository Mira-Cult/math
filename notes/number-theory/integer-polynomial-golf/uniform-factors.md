# A uniform product replacing the four packed comparison factors

Source: `JoseBrox/diophantine-z-q_improvements` at
`fa09c9c6c97982c13265e7088d95cdb61b3e90cf`,
`papers/quartic/quartic262_20261110_v21.tex`, sections
"Plain parameter ratios and the local tests", "Four factors and
extraction at one place", "Integrality before the formal congruences",
and "Simultaneous completeness".

This is an algebraic/valuation modification of that source, retaining
its arithmetic premises, scalar certificate, three comparison scales,
and numerical threshold `N=9682`. It is intended to shorten the
description, not to preserve the source's degree or variable count.

## Replacement

Use the source's field `K=Q(sqrt(2))`, conjugation, elliptic points,
formal-parameter ratios and tests. Explicitly, with `f=1/x`,
`z=-x/y`, root points `Q_i`, numerator points `U_i`, and differences
`V_i=U_i-Q_i`, let

```math
\begin{aligned}
D_H&=f(H),& A_i&=f(U_i),& B_i&=\sigma f(V_i),\\
B_0&=\sigma f(H-P),&
L_i&=z(U_i)/z(H),&
L'_i&=\sigma\bigl(z(V_i)/z(H-P)\bigr),\\
C_i&=L_i-L_i',& I&=L_1-\beta,\\
G&=L_3^2-L_2(L_2-2)L_3L_4+(L_2-2)^2L_4^2-1.
\end{aligned}
```

Here `i=1,2,3,4`. Define two finite lists

```math
\mathcal F=(D_H,A_1,A_2,A_3,A_4,B_0,B_1,B_2,B_3,B_4),
\qquad
\mathcal C=(C_1,C_2,C_3,C_4,I,G).
```

For each of the source's three scales, use the same contact function
`R`, weight `q=R^{-1}-1`, and `gamma=408/409`, but replace the product
of four packed factors by

```math
\boxed{W=\prod_{f\in\mathcal F}(1+q^3 f^2)
             \prod_{c\in\mathcal C}(1+q^5 c^2).}
```

Impose the same pole predicate on

```math
 b=\frac{\gamma^2R}
        {\operatorname{Tr}_{K/\mathbb Q}(W^{-1})^2}.
```

This expression is interpreted with guards on all denominators,
including `R`, `W`, and its reciprocal trace. No condition `q != 0`
is needed for this version, since it uses no inverse powers of `q`.
Retaining that guard is also safe: the constructed witnesses have a
selected contact prime with `v_p(q)=-1`.

## Local lemma

Let `p` be one of the source's consumed contact primes, so it lies
outside the source's exceptional set, `p` is odd and unramified in
`K`, `gamma` is a unit, and

```math
\nu=v_p(R)>0\text{ is odd},\qquad v_p(q)=-\nu.
```

At every place `v` of `K` above `p`, each factor in `W` is nonzero
and has valuation at most zero. If its valuation is zero, its
residue is one. Indeed, for a nonzero field test `t` and odd
`k in {3,5}`, the two term valuations in `1+q^k t^2` are

```math
0\quad\text{and}\quad 2v(t)-k\nu.
```

The second is odd, hence not zero. The valuation of the sum is
their minimum; cancellation is impossible. A zero test leaves the
constant factor one and satisfies every required depth inequality.
In particular `W != 0` at each contact place.

Put

```math
\ell=\max_{v\mid p}v(W)\le0.
```

The trace inequality gives

```math
v_p(\operatorname{Tr}(W^{-1}))\ge-\ell,
\qquad v_p(b)\le\nu+2\ell.
```

The valuation of `b` is odd because `v_p(gamma)=0` and `nu` is
odd. The retained pole obstruction excludes negative odd valuation,
so it is positive. Thus `ell > -nu/2`.

Choose a place attaining `ell`. Every factor has nonpositive
valuation there and their valuations sum to `ell`; each factor
therefore has valuation at least `ell`. Its nonconstant term also
has valuation strictly greater than `-nu/2` (whether its valuation
is positive or is the factor's negative valuation). Consequently

```math
\begin{aligned}
2v(f)-3\nu&>-\nu/2
    &&\Rightarrow& v(f)&>5\nu/4&& (f\in\mathcal F),\\
2v(c)-5\nu&>-\nu/2
    &&\Rightarrow& v(c)&>9\nu/4&& (c\in\mathcal C).
\end{aligned}
```

Since the valuations are integral and `nu>=1`, all ten reciprocal
abscissa tests have order at least two, and all six comparison tests
have order at least three. This supplies every order used by the
source's subsequent logarithmic argument. In particular `C1` and
`I` have more precision than that argument needs.

The trace inequality holds both at split primes and at inert primes.
At a split prime it is the valuation inequality for the sum of the
two conjugate reciprocals. At an inert prime conjugation preserves
the single normalized valuation. Any extra trace cancellation only
strengthens the upper bound on `v_p(b)` and does not invalidate it.

## Transfer of soundness and the numerical constant

The source proves integrality of the plain and full logarithmic
ratios before converting the relative logarithm errors into absolute
congruences. That proof applies unchanged: the new bounds include
all its hypotheses. It gives each comparison contact radical to
the third power dividing the Lucas residual, and at least the first
power dividing the reduced input residual.

The contact-height bounds and effective abscissa-sum height bound
depend on the same three scales, contact set, and elliptic labels;
none depends on the number or degree of the packed factors. The
scalar certificate is unchanged. Therefore every displayed height
and integer threshold inequality in the source's soundness section
still applies. In particular **`N=9682` remains sufficient** under
the source's inherited premises. No new height conjecture or larger
fixed parameter is required.

## Transfer of completeness

Use the same prime selection, elliptic labels and shared index as in
the source's completeness proof. At every selected contact prime,
`v_p(q)=-1`. At the selected place all reciprocal abscissas in
`F` have valuation at least two and all comparison expressions in
`C` have valuation at least four. Hence

```math
v(q^3f^2)\ge1,\qquad v(q^5c^2)\ge3,
```

so every factor has residue one and `W` has residue one. At the
opposite place each factor has nonpositive valuation and residue
one if its valuation is zero, as in the local lemma. Thus the
reciprocal trace is a unit with residue one or two. (The selected
primes are odd.) The comparison pole input has valuation one at
every selected contact prime, exactly as in the source.

At the finitely prepared places the source chooses the contact
parameter with sufficiently negative valuation that `R -> 1` and
`q -> 0`. The field tests lie in fixed prepared neighborhoods and
are bounded below in valuation. The new factors therefore tend to
one and the reciprocal trace tends to two. The same finite
congruence preparation gives the local squareclasses and depth
conditions required by pole realization at `2,3,17`.

The square-denominator assertion also persists. Away from selected
contact primes the valuation of `R` is even. Multiplication by
`gamma^2` and division by a squared rational trace preserve parity,
regardless of the values of the new factors. At selected primes
the valuation of the pole input is positive one. This gives the
same square reduced denominator.

For real preparation, the source sends the positive slope to
infinity, with every elliptic test staying in a fixed compact real
neighborhood. Then `R -> 1`, `q -> 0+`, every factor is positive
at both real embeddings, and `W -> 1`. The pole input therefore
tends to

```math
\gamma^2/4=41616/167281\in(0,17),
```

which is the source's same interior limit. The inherited pole
realization then supplies its rational witnesses.

These completeness witnesses have `R != 0`, `W != 0` and
`Tr(W^{-1}) != 0`: the first follows from positive large contact
parameter, and the latter two follow already from positivity at
the real embeddings (and also from their unit computations at any
selected prime). Guards on these quantities thus remove no needed
complete witnesses.

## Rational pole equations

For clarity, the zero-preparation pole predicate itself can be
represented with four rational witnesses `e,p,q0,s` and two equations:

```math
\begin{aligned}
B&=17b,& h_0&=e(B-b^2),\\
p^2&=B(1-e)(1+3e),&
Bq_0^2&=(s^2-Bh_0)(s^2+3Bh_0).
\end{aligned}
```

Here `B` and `h0` are expressions, not extra quantified variables.
The pole input must be nonzero. The scalar input is positive by
the unchanged source argument; each comparison input is nonzero
on the rational-expression guard locus. No new nonzero condition
on the four pole witnesses is imposed, so this implementation does
not need a strengthened nonzero-witness premise.

## Review scope

The local replacement proof above is elementary and independent of
the source's packed-factor proof. Its implication to integrality
still uses the source's stated global arithmetic premises. It does
not independently validate those premises or the entire H10(Q)
argument.
