# CVP-M10: coded channels charge whole local moment vectors

Date: October 11, 2026.

Claim status: complete elementary proof of the code and local rank/weight
transformation. The end-to-end use imports the explicitly stated atomization
and source-decoding theorem of `PACKED_TWO_LEVEL_FOLD.md`; this note does not
independently certify that imported theorem. Exact regressions are component
checks, not formal verification or peer review.

Registry impact: refinement of the existing CVP-M10 construction, with no new
source-soundness interface and no new lane. The assembled construction packet
owns the registry/status update.

## 1. Finite theorem

For every integer channel count C >= 1, one can deterministically construct,
in time polynomial in C, binary linear maps

    E_code : F_2^C -> F_2^M,
    R_code : F_2^M -> F_2^C

such that

    R_code E_code = identity,
    C <= M <= 32 C,
    wt(E_code v) >= d_code > M/8 for every nonzero v.

The construction and an explicit integer lower bound on d_code are given in
Section 2. The maps are computed before constructing the source affine system.
They depend only on C, not on any satisfying assignment.

Let a local vector moment table be indexed by tuples u and channels c, with
decoded site vector z_u in F_2^C. Over any field F of characteristic two, form

    V_((a,c),b) = sum_u z_(u,c) phi_a(u) psi_b(u).

Here phi_a and psi_b are any fixed F-valued functions; no assumed atomic
representation, polynomial interpolation, or source semantics is needed.

Replace every local vector z_u by M measured binary variables w_u and impose

    w_u = E_code R_code w_u,
    z_u := R_code w_u.

The second line defines a vector of linear forms; it introduces no free
witness variables. For EVERY assignment satisfying the displayed membership
equations,

    sum_u wt(w_u) >= d_code rank_F(V).                 (1.1)

Proof: each u contributes the outer product

    (z_(u,c) phi_a(u))_(a,c) (psi_b(u))_b^T.

It has rank at most one, and it vanishes if z_u=0. Therefore

    rank V <= #{u : z_u != 0}.

On the code image, w_u=E_code z_u, so every such nonzero site has weight at
least d_code. Summing proves (1.1). All possible cancellations only decrease
rank. The bound concerns arbitrary binary site vectors, not singleton or
source-valid witnesses.

## 2. An elementary explicit binary code

Put

    m = ceil(log_2(2C)), k = ceil(C/m), q_code = 2^m.

For C >= 1, m <= C and 2k <= 2C <= q_code. Work over the field F_(2^m),
constructed deterministically by enumerating monic binary polynomials and
testing irreducibility. Since 2^m < 4C, even enumeration takes polynomial
time in C.

### 2.1 Inner binary map

We construct a binary linear map

    B : F_2^m -> F_2^(8m)

whose nonzero outputs have weight at least 2m+1. Its output bits are inner
products with successively chosen rows g_1,...,g_(8m) in F_2^m.

After j rows, write w_j(v) for the output weight on v != 0 and consider

    U_j = sum_(v != 0) 2^(-w_j(v)).

For a uniformly averaged candidate next row g, every nonzero v has equally
many rows with inner product zero and one. Thus

    average_g sum_(v != 0) 2^(-w_j(v)-<g,v>) = (3/4) U_j.

Choose the lexicographically first row minimizing this finite sum. It follows
deterministically that

    U_(8m) <= (2^m-1)(3/4)^(8m).

Multiplying by 2^(2m),

    sum_(v != 0) 2^(2m-wt(Bv))
      <= (2^m-1)2^(2m)(3/4)^(8m)
      < [8(3/4)^8]^m
      = (6561/8192)^m
      < 1.

If a nonzero v had weight at most 2m, its single summand would be at least
one. This contradiction proves wt(Bv) >= 2m+1. In particular, B is injective.

This is a polynomial algorithm: at each of 8m steps enumerate 2^m candidate
rows and 2^m-1 nonzero messages. All scores are computed exactly, after
multiplication by their common power-of-two denominator. The integers involved
have O(m) bits. No random seed or exponential search in C is present.

### 2.2 Outer polynomial evaluation and concatenation

Pad the C input bits by zeros to km bits, group them into k field elements,
and regard these as the coefficients of a polynomial of degree less than k.
Evaluate it at 2k distinct elements of F_(2^m), then apply B to the binary
expansion of each evaluation.

Every nonzero input polynomial is nonzero on at least k+1 evaluation points:
its degree is at most k-1, so it has at most k-1 roots among the 2k points.
The concatenated binary map therefore has

    M = 16km,
    d_code >= (k+1)(2m+1) > 2km = M/8.

Moreover,

    km <= C+m-1 <= 2C,
    M <= 32C.

Both evaluation and the inner maps are binary linear. Their composition with
zero padding is injective, so Gaussian elimination constructs a binary-linear
left inverse R_code. Only the equation R_code E_code=identity is needed; the
decoder is allowed to have arbitrary values off the code image.

The membership condition

    w = E_code R_code w

is exactly equivalent to w being in the code image. In particular it eliminates
nonzero w in the kernel of the decoder. These membership equations are an
essential part of the new affine compiler.

## 3. Substitution into the packed two-level compiler

Use exactly the decoded channel count C, field tower, local tuple set and
moment definitions from `PACKED_TWO_LEVEL_FOLD.md`. At every site

    (zeta,t,u) in H x F x F^r,

replace C binary table coordinates by M coordinates w_(zeta,t,u). Impose the
sitewise code-image equations, and substitute R_code w for the old decoded
channel vector in EVERY old equation and moment definition.

All equations remain binary affine. In particular:

- polynomial interpolation and its high-coefficient tests remain binary linear;
- Frobenius remains binary linear;
- the source maps LA, LB, membership in I, and Gamma remain binary matrices
  applied to the original decoded channel vectors;
- the original source semantics never apply a merely binary-linear map to an
  assembled extension-field moment.

No old semantic equation is dropped, weakened or replaced by a codeword
promise. Code membership is an additional emitted linear constraint.

Let

    S = Qq,
    S_minus = (q-d_in)(Q-d_out) >= S/4,
    t0 = rank_E(Hglob).

The two polynomial rank-sampling inequalities in the original construction
remain unchanged:

    sum_zeta rank_H(J_zeta) >= (Q-d_out)t0,
    sum_t rank_F(V_(zeta,t)) >= (q-d_in)rank_H(J_zeta).

Apply (1.1) at every local sampling pair (zeta,t), and sum. This gives the
new arbitrary-witness bound

    W_encoded >= d_code S_minus t0.                  (3.1)

For the honest assignment x, the original construction places the SAME binary
vector sigma(x) at one tuple u for each pair (zeta,t), and zero elsewhere.
It is nonzero because the mass entry is one. Replace that vector by
E_code sigma(x). Every old equation remains satisfied, and

    W_Y <= M S.                                      (3.2)

Every encoded feasible witness with

    W_encoded < d_code K S_minus

has t0<K by (3.1). Decoding yields a feasible table for the same packed source
constraints. The common-atom/source-decoding argument, once its imported
finite-window theorem is established, yields a genuine satisfying assignment.
Consequently an unsatisfiable source obeys

    W_NO >= d_code K S_minus > M S K/32.              (3.3)

Thus the affine Hamming gap is at least a constant times K, and the exact
parity-kernel Euclidean gap is at least sqrt(K/32), before rounding the YES
radius. Rounding changes only a fixed constant. No inequality here restricts
integer representatives: the final lattice distance is exactly the minimum
binary coset weight.

The measured binary coordinate count, hence the full lattice rank, is

    D = M q^(r+h+1) <= 32 C q^(r+h+1).

The code multiplies ambient rank by at most 32. It improves the NO squared
distance by a factor of order C because an entire nonzero channel vector now
costs order C, while its contribution to the local vector-Hankel rank is one.

## 4. Exact rank-degree consequence

Write delta=1/(h-1) and retain the old scaling

    C=Theta_(r,h)(N log N),
    S=Theta_(r,h)(N^(1+2delta)),
    K=s^r=Theta_(r,h)(N^(r delta)),
    q^r=Theta_(r,h)(N^(r delta)).

The new ledger is

    D=O_(r,h)(N^(r delta+2+2delta) log N),
    W_Y=O_(r,h)(N^(2+2delta) log N),
    W_NO=Omega_(r,h)(N^(r delta+2+2delta) log N),
    gap=Omega_(r,h)(N^(r delta/2)).

Therefore

    p0=(r+2h)/(h-1),
    c0=r/[2(r+2h)],
    (1/2-c0)p0=h/(h-1).

For every fixed c<c0, strict exponent slack absorbs the constant factors and
the logarithm in D. The leading inverse-deficit constant tends to one as h
increases. This is a rank-degree statement; the running-time exponent is
polynomially related and is not asserted to equal p0.

### 4.1 Why r>=1 is sufficient

The earlier proof assumes r>=h to ensure its old, weaker gap exponent is
positive. Its construction, interpolation bounds and soundness arguments need
only r>=1. In particular, for 0<=a<s^r and 0<=b<=4s^r, the sum of the two
radix-s digit sums is bounded by

    r(s-1)+(r-1)(s-1)+4s
       = (2r+3)s-(2r-1)
       < (2r+4)s = Delta.

This includes r=1, where the sole digit is the unbounded top digit. The field
size inequalities use Delta and h>=2 and do not require r>=h. The protected
moment window remains K=s^r and L=4K. With coding, c0 is positive for every
r>=1.

### 4.2 A schedule covering the whole interval 0<epsilon<1/2

Let h be the least power of two satisfying h>=1+4/epsilon, and set

    r=floor(h/epsilon-2h)+1.

Then r>=1 and c0>1/2-epsilon. Also,

    p0 <= 1/epsilon+(1/epsilon+1)/(h-1)
       <= 1/epsilon+1/4+epsilon/4
       < 1/epsilon+3/8.

Absorbing the logarithm into the remaining fixed exponent slack gives

    D=O_epsilon(N^(1/epsilon+1)).

The r<h cases are intentional and necessary for this clean schedule near
epsilon=1/2. Restricting to r>=h would impose an unnecessary parameter loss.

## 5. Reproducible component regressions

Run from the repository root:

    python3 experiments/check_coded_channels.py \
      --output experiments/certificates/coded_channels.json

The checker uses only exact integers, rational numbers and finite fields. It
constructs the greedy inner maps, exhausts the concatenated codes for small
channel counts, verifies a full ambient membership space for the smallest
code, checks the local rank/weight inequality on every specified binary table
over F_2 and F_4, checks signed residuals of every 2x3 binary affine system,
and verifies the exponent schedule including epsilon close to one half.

The certificate records the complete tested parameter lists, counts and the
checker SHA-256. These finite checks do not replace the mathematical proofs
above or the imported common-atom and source-decoding proofs.
