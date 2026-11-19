# Why the tree partition inequality does not extend to every cycle

**Mira Cult · 16 November 2026**

This is an exact energy-level counterexample, not a Boolean Fourier or FEI
counterexample. The related Boolean cycle target remains open. The complete
calculation received a scoped nonauthor model review; see [verification](VERIFICATION.md).

[Overview](README.md) · [Open targets](OPEN_PROBLEMS.md)

Scientific source: [72102dbe92e277f6d616f6a1201d5388992e5dd3](https://github.com/Mira-Cult/math-wip/blob/72102dbe92e277f6d616f6a1201d5388992e5dd3/problems/0298-fourier-entropy-influence-conjecture/manuscripts/cyclic_partition_obstruction.md).

The [affine-forest theorem](affine-forests.md) uses, for a nonconstant
connected integer tree energy E,

```math
 Z(E)=\sum_s4^{E(s)-\min E}\ge2\,5^{\kappa(E)},\qquad
 \kappa(E)=n-\deg_{\mathbb F_2}\mathbf1[E=\min E].
```

The following proposition shows that the same statement fails already on
one cycle. It also identifies a Boolean arithmetic restriction omitted by
that failed extension.

**Proposition.** On four binary variables, put

```math
 v(s)=s_2+s_3-s_1s_2-s_2s_3-s_3s_4+s_1s_4.
```

Its minimal interaction graph is the cycle 12,23,34,14. It has
`kappa(v)=2` but `Z(v)=40<50=2*5^kappa(v)`. The probability law
`p(s)=4^v(s)/40` has no Boolean Fourier signing. This remains true after
adjoining any number of independent fair spectral coordinates and applying
an injective affine spectral map.

**Proof.** Set `x_i=1-2s_i`. Expansion gives

```math
 1-2v=\frac{x_1x_2+x_2x_3+x_3x_4-x_1x_4}{2}.
```

If x2=x4, the right side is x2*x3; if x2=-x4, it is x1*x2. Thus it is
always a sign. In each case it is balanced over the remaining independent
bits. Consequently v takes values zero and one eight times each. All four
edge coefficients are nonzero, so the minimal graph is exactly the stated
cycle. The ground indicator over F2 is

```math
 1+v=1+s_2+s_3+s_1s_2+s_2s_3+s_3s_4+s_1s_4,
```

of degree two. Hence kappa=4-2=2, and

```math
 Z=8+8\cdot4=40\lt 2\cdot5^2.
```

Every Fourier coefficient of a Boolean function on a finite cube is a
dyadic rational. Every squared coefficient therefore has a reduced
denominator which is a power of two. The displayed law has atoms 1/40
and 1/10, with an odd factor five in their reduced denominators. No
choice of Fourier signs can change those squared coefficients. Adding
q independent fair spectral coordinates replaces each atom by its value
divided by 2^q, retaining the odd denominator. An injective affine map
only relabels these atoms. This proves all the nonrealizability assertions.
QED.

This does not exclude nonuniform or correlated Boolean completions that
change the atom probabilities. The arithmetic obstruction is part of the
reason a probability-only extension is too strong. A Boolean-sensitive
cycle theorem must retain the power-of-two norm and the actual Walsh
signing identities; the proposition does not refute such a theorem.

A distinct limitation of affine-forest coverage is immediate. For any
positive law let `Per(p)={a:p(s+a)=p(s) for every s}`. This is a linear
subspace, and the law is uniform on every coset of it. An n-bit rare-point
phase for n>=3 has a unique largest atom, so its period subspace is zero.
Every positive Boolean forest in positive dimension has a nonzero fair
period by the fair-rank theorem. Hence no invertible affine spectral
change puts this rare-point law in the positive-forest class. The separate
one-atom and point-modification mechanisms cover it; affine closure alone
cannot be universal.

The immediate restricted structural target is a period-dimension/entropy
bound for actual positive Boolean **pairwise** cycle spectra. Such a bound
would extend the affine argument for that class. It is not asserted for
all positive laws, for arbitrary triangle potentials, or as an equivalent
reformulation of full FEI.

## Reproducibility

Run from the repository root:

```sh
python notes/combinatorics/fourier-entropy-influence/code/check_cyclic_partition_obstruction.py
```

The program checks every one of the sixteen energy values, the sign
identity, the ground-indicator algebraic normal form, and the integer
partition inequality. Boolean nonrealizability is proved analytically
above, not decided by finite signing enumeration.
