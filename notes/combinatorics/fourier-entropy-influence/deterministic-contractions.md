# Deterministic spectral contractions

**Mira Cult · 16 November 2026**

Fixed spectral coordinates and deterministic equality/complement relations
can be removed while preserving Boolean realizability and Fourier entropy,
and without increasing influence. The resulting positive forest quotient
therefore inherits the constant-four theorem. A genuinely three-state
edge support is a different constraint and is not covered.

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

## 1. All deterministic spectral edges can be contracted

**Proposition 1.** Suppose the squared Fourier law of Boolean f factors over
a forest. Delete spectrally deterministic coordinates and contract every
remaining edge whose pair marginal has support of size two. There is a
Boolean function g on the resulting coordinates such that

    H(g)=H(f),   I(g)<=I(f),

and its squared Fourier law factors over the contracted forest. Consequently,
if the remaining edge marginals all have full support, then

    H(f)<=4I(f).                                         (1)

In particular this extends the constant-four conclusion to forest supports
whose hard constraints are deterministic equality or inequality relations,
in addition to fixed spectral coordinates. Three-state edge supports are
not included in this corollary.

**Proof.** A two-state binary pair marginal either fixes one of its
coordinates or imposes equality or inequality between the two bits. After
removing all globally fixed coordinates, the latter are the only cases.
Each connected component C of these deterministic edges can therefore be
written

    s_i=a_i xor z_C,   i in C,

for a single free binary coordinate z_C and fixed offsets a_i. Components
with a forced vertex are themselves forced and are removed. The remaining
components are disjoint. Write r_C=|C| and a_C=sum_(i in C)a_i. Spectral
support is contained in the affine injection

    s(z)=a xor (xor_C z_C 1_C),

including the fixed coordinates in a. If the coefficient at s(z) is b_z,
Fourier inversion gives

    f(x)=chi_a(x) g(y),
    g(y)=sum_z b_z chi_z(y),
    y_C=product_(i in C)x_i.

The map x->y is onto, since the C are disjoint nonempty blocks. Hence g is
Boolean. The nonzero Fourier coefficients are in bijection, so entropy is
unchanged.

Choose each quotient orientation so that a_C!=r_C: if all offsets are one,
flip z_C and complement every offset in C. Let q_C=Pr(z_C=1). The original
component's expected spectral degree is

    a_C(1-q_C)+(r_C-a_C)q_C.

If a_C=0 this is r_C q_C>=q_C. If 1<=a_C<=r_C-1, both endpoint degrees are
at least one, so this expectation is at least 1>=q_C. Fixed-one coordinates
only add to the original influence. Summing proves I(g)<=I(f).

Substitution of the deterministic relations in a unary/edge factorization
turns internal component factors into unary factors, while every surviving
edge joins two contracted components. Contracting edges and deleting fixed
vertices cannot create a cycle. Thus the quotient law still factors over a
forest. If all its edge marginals have four positive states and all its
remaining unary marginals have two positive states, every factor can be
taken positive on every state: an actual zero in a unary or edge factor
would force a zero in that marginal. The quotient law then has full support.
Apply the established positive-forest theorem H(g)<=4I(g). The quotient
may have no variables, in which case it is a character before removal and
both its entropy and its quotient influence are zero. ∎
