# CVP-M10: finite Hankel atomicity with a self-contained proof

**Research lane:** CVP-M10 / SymmetricMultilinearFold  
**Date:** 2026-10-11  
**Claim ID:** CVP-M10-HANKEL-1  
**Status:** complete mathematical proof, independently rederived during a
model-assisted audit; not a formal certificate or human expert review.  
**Purpose:** supply the exact common-atom dependency needed by the packed
two-level compiler, without relying on an inaccessible external repository.

The proof applies directly to vector moments and also to rectangular matrix
moments. It uses finite-dimensional linear algebra, Cayley-Hamilton, and a
principal ideal in one polynomial variable. The construction need not promise
an infinite recurrence, a flat extension, or an atomic population.

## 1. Exact finite theorem

Let `F` be any field of characteristic two. Fix positive integers `k,m,n`
and an integer `L>=0`. Suppose matrices

```text
M_0,...,M_(k-1+L) in Mat_(m x n)(F)
```

are given. Form the rectangular block-Hankel matrix

```text
H_((a,i),(b,j)) = M_(a+b)(i,j),
0<=a<k, 0<=b<=L, 1<=i<=m, 1<=j<=n.
```

Write `t=rank_F H`. Assume

```text
t<k,
L>=max(t,2t-2),
M_(2e)=M_e^[2] for every 0<=e<t.                    (1.1)
```

Here `^[2]` squares entries separately; it is not matrix multiplication.
For `t=0` the Frobenius condition is empty and the numerical condition is
interpreted over integers. All moments read by (1.1) lie in `0,...,L`.

**Theorem.** Over an algebraic closure `Fbar`, there are distinct elements
`alpha_1,...,alpha_u`, with `0<=u<=t`, and nonzero matrices

```text
C_1,...,C_u in Mat_(m x n)(F_2)
```

such that

```text
M_e = sum_(l=1)^u alpha_l^e C_l, 0<=e<=L.           (1.2)
```

The root zero is allowed, with the usual convention `alpha^0=1`. An empty
sum means the zero matrix.

The theorem reconstructs the protected prefix `0,...,L`. It does not claim
to reconstruct the last `k-1` moments of the supplied window, or to make
`u=t`. For example, a sequence zero except at the last supplied moment can
have positive Hankel rank and a zero protected prefix.

### Corollary used by the CVP compiler

Let `K>=1`, take `k=K,L=4K`, and give moments through `5K-1`. If

```text
rank H=t<K,
M_(2e)=M_e^[2] for 0<=e<K,
```

then (1.2) holds for `0<=e<=4K`, and in particular for `0<=e<=K`, with
fewer than `K` common atoms. Indeed,

```text
4K>=max(t,2t-2)
```

and the emitted Frobenius equations include every equation used in (1.1).
For vector moments use `n=1`; square padding is unnecessary.

## 2. A row plateau makes every available shift well-defined

For `0<=s<=k`, let `H_s` denote the first `s` row blocks of `H`, retaining
all `L+1` column blocks. Put `r_s=rank H_s`, so `r_0=0` and `r_k=t`.

Since `t<k`, there is an index

```text
1<=s<=t+1<=k with r_s=r_(s-1).                    (2.1)
```

Otherwise all first `t+1` rank increments would be positive integers and
`r_(t+1)>=t+1`, a contradiction.

For every column-block index `0<=b<=L` and input index `1<=j<=n`, write

```text
w_(b,j) = (M_b e_j, M_(b+1)e_j, ...,
             M_(b+s-1)e_j) in (F^m)^s.
```

Let `W` be their span and `d=dim W=r_s<=t`. Let `P` delete the last output
block and let `Q` delete the first output block. When `s=1` these maps have
zero-dimensional codomain. Since the image of `P` on `W` is exactly the
column space of `H_(s-1)`, (2.1) says

```text
P|_W is injective.                                  (2.2)
```

The overlapping moment windows obey

```text
P(w_(b+1,j)) = Q(w_(b,j)), 0<=b<L.                 (2.3)
```

Consider any relation involving only blocks before the last one:

```text
sum_(b<L,j) a_(b,j) w_(b,j)=0.
```

Apply `Q`, use (2.3), and then use injectivity (2.2). The result is

```text
sum_(b<L,j) a_(b,j) w_(b+1,j)=0.                  (2.4)
```

Thus shifting a finite column relation by one is legitimate. This supplies
the missing well-definedness argument; no global recurrence has yet been
assumed.

## 3. A column plateau gives a finite state-space realization

Let

```text
W_b=span{w_(a,j):0<=a<=b, 1<=j<=n}, W_(-1)=0.
```

There is a plateau `W_b=W_(b-1)` for some `0<=b<=t`: there are `t+1`
possible inclusions beginning at the zero space, whereas all dimensions are
at most `d<=t`. These indices are available because `L>=t`.

Once a plateau occurs, it persists through the supplied column window.
Indeed, express every `w_(b,j)` in the preceding column blocks. If `b<L`,
shift those relations using (2.4). This expresses every `w_(b+1,j)` in
blocks `1,...,b`, which are already in `W_b`. Continue inductively.
For a plateau at `b=0`, the same argument starts with all `w_(0,j)=0`.

Consequently

```text
span{w_(b,j):0<=b<L}=W.                            (3.1)
```

If `L=0`, the hypotheses force `t=d=0`, which is the zero case below.

Equations (2.4) and (3.1) now define an endomorphism

```text
A:W->W, A w_(b,j)=w_(b+1,j) for every b<L.        (3.2)
```

Let `B:F^n->W` send `e_j` to `w_(0,j)`, and let `C:W->F^m` read the first
output block. Induction using (3.2) gives

```text
M_e=C A^e B, 0<=e<=L.                              (3.3)
```

If `d=0`, all matrices in this protected prefix are zero, so the theorem
holds with no atoms. Otherwise choose a basis of `W` and define the infinite
extension

```text
S_e=C A^e B, e>=0.                                 (3.4)
```

Its state dimension is `d<=t`. Only (3.3), which was derived from the finite
window, identifies this extension with the original moments.

## 4. The finitely many Frobenius equations extend to all indices

Let

```text
p(X)=det(XI-A)
```

be the monic characteristic polynomial of degree `d`. Write `p^[2]` for
the polynomial obtained by squaring its coefficients, without changing its
exponents. In characteristic two,

```text
charpoly(A^2)=p^[2]=charpoly(A^[2]).                (4.1)
```

The right identity follows directly by squaring the coefficients in the
determinant expansion. For the left identity, compute

```text
det(X^2 I-A^2)
 =det((XI-A)^2)
 =det(XI-A)^2
 =p(X)^2
 =p^[2](X^2).
```

Substitution `X -> X^2` is injective on polynomials, proving the claim.

Consider the Frobenius defect sequence

```text
D_e=S_(2e)-S_e^[2]
   =C(A^2)^e B - C^[2](A^[2])^e B^[2].            (4.2)
```

By Cayley-Hamilton and (4.1), both terms in (4.2), and hence their
difference, satisfy the same monic order-`d` recurrence `p^[2]`. The order
does not double when the two terms are subtracted.

For `0<=e<d`, both `e` and `2e` lie in the protected prefix, because

```text
2d-2<=2t-2<=L.
```

Equations (1.1) and (3.3) therefore give `D_e=0` for the first `d` indices.
The monic recurrence propagates this zero initial segment, yielding

```text
S_(2e)=S_e^[2] for every e>=0.                     (4.3)
```

This is where the finite Frobenius horizon is used. Requiring `2d`
initial defects would unnecessarily lose the available hypothesis.

## 5. Frobenius makes the joint recurrence ideal radical

Extend scalars to an algebraic closure `Fbar`, which does not increase `d`.
Let `I` be the ideal of all common scalar recurrence polynomials:

```text
I={f(X)=sum_i f_i X^i :
       sum_i f_i S_(e+i)=0 for every e>=0}.
```

It is an ideal because addition and scalar multiplication preserve these
identities and multiplication by `X` shifts their index. Cayley-Hamilton
shows `p in I`, so this ideal is nonzero and has a monic generator `g`
with

```text
deg g<=d.                                          (5.1)
```

Suppose `f^2 in I`. For every `e`, use characteristic two and (4.3) to get

```text
(sum_i f_i S_(e+i))^[2]
 =sum_i f_i^2 S_(e+i)^[2]
 =sum_i f_i^2 S_(2e+2i)
 =0.
```

Squaring is injective in a field, entry by entry, so `f in I`. Thus the
ideal is closed under taking square roots. This already forces its generator
to be squarefree: if `(X-alpha)^2` divided `g`, then

```text
f=g/(X-alpha)
```

would have lower degree than `g` while `f^2` was divisible by `g`. That would
give `f^2 in I`, hence `f in I`, a contradiction.

Equivalently, `I` is radical: if `f^a in I`, take a power of two at least
`a`, multiply by the additional power of `f`, and repeatedly take square
roots. No assumption of positivity or nonsingular moment anchoring appears.

## 6. Split the squarefree recurrence and recover binary coefficients

If `g=1`, every `S_e` is zero and the conclusion is immediate. Otherwise,
write its distinct roots as

```text
g(X)=product_(l=1)^u (X-alpha_l), u=deg g<=d<=t.
```

Vandermonde inversion on indices `e=0,...,u-1` gives unique coefficient
matrices `C_l` such that

```text
S_e=sum_l alpha_l^e C_l, 0<=e<u.
```

Both sides satisfy the monic recurrence `g`. Hence they agree for every
`e>=0`. No `C_l` can be the zero matrix: otherwise omitting that root would
produce a common recurrence polynomial of degree below `deg g`.

Now apply (4.3):

```text
0=S_(2e)-S_e^[2]
 =sum_l (alpha_l^2)^e (C_l-C_l^[2]).
```

The elements `alpha_l^2` remain distinct in characteristic two. A second
Vandermonde inversion yields

```text
C_l=C_l^[2] for every l.
```

Every coefficient entry satisfies `x^2=x`, whose roots in a field of
characteristic two are exactly zero and one. Therefore the matrices are
entrywise binary. Restrict the infinite identity back to (3.3) to obtain
the finite conclusion (1.2). This completes the proof.

## 7. How this applies to the packed compiler

For the packed two-level construction, `M_e` is the column vector with one
entry per binary coefficient channel. Its actual charged matrix is

```text
Hglob_((a,c),b)=m_(a+b,c), a<K, b<=4K.
```

Apply the theorem with `m` equal to the channel count and `n=1`. The
two-level determinant estimate gives the required hypothesis

```text
W<K(q-d_in)(Q-d_out) => rank Hglob<K.
```

The new theorem then gives one common atom set of size below `K`, with one
binary vector per atom. It introduces no new witness coordinates or emitted
equations. Identifier, symmetry, channelwise source equations, and the mass
equation remain responsible for source validity; atomicity alone does not
assert that any atom satisfies the source.

For the earlier symmetric multilinear construction, the moments are the
full `(N+1) x (N+1)` blocks. The rectangular-matrix version proved above
applies directly to its charged block-Hankel matrix, retaining the bound
`u<=t` without flattening its entries and inflating rank.

## 8. Resource and confidence boundary

This is a mathematical extraction theorem used in the soundness proof. The
compiler does not compute the state space, roots, or atomic decomposition.
Its ambient-coordinate, equation, completeness-radius, NO-threshold, and
runtime ledgers are therefore unchanged. In particular, no enumeration of
the algebraic closure is required by the reduction.

The proof removes the external common-atom theorem as an unresolved retrieval
dependency for these two constructions. It does not by itself change their
hardness exponents or constitute a formal verification of their compilers.

The focused finite checker is
`experiments/vector_hankel_atomicity_check.py`. Its small-field exhaustive
cases and boundary-spike examples are regressions rather than proof premises.

## Project references

- `docs/PACKED_TWO_LEVEL_FOLD.md`, Sections 4, 5, 7 and 8.
- `docs/SYMMETRIC_MULTILINEAR_FOLDED_ATOMIZER.md`, Sections 2.2 and 12.
- `reviews/2026-10-11_CVP-M10_vector-atomicity-audit.md`.

