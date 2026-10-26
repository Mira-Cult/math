# CVP-M10: trim the sampling grids without weakening the gap

**Research lane:** CVP-M10 / SymmetricMultilinearFold  
**Refinement:** TrimmedCodedFold, within the existing coded-fold construction  
**Date:** October 11, 2026  
**Predecessor:** `CODED_PACKED_TWO_LEVEL_FOLD.md`, PR #369  
**Claim status:** complete mathematical proof draft; model-assisted audits are
recorded separately. No formal verification or human expert review is claimed.

## 1. Positive result

The preceding compiler samples every point of F_q at the inner level and every
point of F_(q^h) at the outer level. Neither interpolation nor the determinant
rank estimate requires using the entire field. We can use exactly twice the
relevant degree bound at each level.

Write

    d_in=(h-1)Delta, d_out=(n-1)Delta,
    T=2d_in, R=2d_out.

For every admissible finite parameter tuple, the new compiler has

    D_trim=M R T q^r,
    W_Y<=M R T,
    W_NO>M R T K/32,
    rho=ceil(sqrt(M R T)),
    dist_NO/rho>sqrt(K/128).                         (1.1)

The NO statement covers every feasible binary word, and the same exact
parity-kernel handoff covers every integer representative. Thus the strictly
sufficient condition for the requested factor is still

    K>128 D_trim^(1-2epsilon).                      (1.2)

At every parameter tuple used by the preceding compiler, this preserves its
certified gap while reducing the lattice rank by the exact factor

    D_old/D_trim = q^(h+1)/(R T).                   (1.3)

For the preceding size rules, the reduction factor has the uniform lower bound

    D_old/D_trim > 4[16h(2r+4)]^(h-1).              (1.4)

For example, the previous simple epsilon=1/10 schedule has h=64,r=513.
Its rank decreases by more than 10^380, at the same K, before any further
parameter optimization. This is a ratio of the actual dimension formulas;
no enormous lattice was constructed to obtain it.

The new optimized schedule is proved in `TRIMMED_FOLD_PARAMETERS.md`. It keeps
the leading inverse-deficit coefficient one and gives an explicit leading
constant in the subpolynomial overhead. The proof below establishes the exact
finite compiler on which that optimization depends.

## 2. Exact admissibility conditions

Use the same sparse quadratic source and its packing as the coded predecessor.
Let N>=8 bound the source variables, equations and monomial list. Let

    h>=2 and s>=2 powers of two, r>=1 an integer,
    K=s^r, Delta=(2r+4)s,
    ell=least power of two >=2N,
    n=4h ell,
    q a power of two, Q=q^h.

In addition to these discrete parameter conditions, require only the two
actual field bounds

    T=2(h-1)Delta<=q,
    R=2(n-1)Delta<=Q.                              (2.1)

There is no need to retain the older sufficient condition s^(h-1)>=N when
checking a new schedule. Its purpose was to imply the second field bound;
the new schedule proves that bound directly.

Construct the compatible fields

    F=F_q < H=F_(q^h) < B=F_(q^(h ell)) < E=F_(q^n)

with the same power bases and source maps as the predecessor. In particular,
the semantic vector has

    C=16h ell log_2 q

binary channels. Use the explicit code G:F_2^C->F_2^M and its left inverse
R_code from `CODED_CHANNELS_LEMMA.md`, so

    C<=M<=32C, d_code>M/8, R_code G=I.

The notation R for the outer sample count is distinct from R_code. The code
construction and all semantic source maps are unchanged.

The monomial-list interpolation needs more source evaluation points than the
number of listed monomials. This follows automatically from (2.1), because
Q>=R=2(n-1)Delta>N. The remaining source-packing condition ell>2R_src-2 also
holds by the definition of ell.

For power-of-two h, the explicit field construction is precisely the quadratic
tower construction already proved in the predecessor. The accompanying
optimized schedule retains this restriction, so it imports no new finite-field
construction theorem.

## 3. Recompile on the selected samples

Fix deterministic enumerations of F and H using their binary bases. Let

    I={the first T elements of F},
    O={the first R elements of H}.

All selected points are distinct. No randomness or source-dependent hitting
set is used. At each site

    (zeta,t,u) in O x I x F^r

introduce an M-bit measured vector w. Emit membership w=G R_code w and set
z=R_code w as derived binary linear forms.

The tuple domain is still all F^r. It is the two sampling domains that shrink.
The exact measured length and full lattice rank are therefore

    D_trim=M R T q^r.                              (3.1)

For the same radix-s monomials phi_a, build

    V_(zeta,t)((a,c),b)
       =sum_u z_(zeta,t,u,c) phi_a(u)phi_b(u),
    0<=a<K, 0<=b<=4K.

For each entry, interpolate its T values over I by the unique polynomial of
degree<T. Emit vanishing of coefficients above the entry's original allowance
(h-1)d(a,b), and evaluate at omega to obtain J_zeta in H.

Next interpolate the R values J_zeta over O by the unique polynomial of
degree<R. Emit vanishing of coefficients above (n-1)d(a,b), and evaluate at
eta_E to obtain the global moment matrix.

The allowances satisfy

    (h-1)d(a,b)<d_in<T,
    (n-1)d(a,b)<d_out<R.

In particular, both interpolants are unique on the allowed polynomial spaces.
Every map in this procedure is a fixed binary-linear map on the measured
coordinates. Interpolation coefficients and moments are derived forms, not
additional variables.

Emit all of the predecessor's Hankel, Frobenius, identifier, symmetry,
channelwise source and mass equations on these derived moments. The finite
moment horizons and the source equations do not change.

This is a recompilation with new interpolation maps. Arbitrarily deleting
coordinates from the old affine system would not describe this construction.

## 4. Rank sampling works on any distinct subset

**Lemma.** Let A(X) be a rectangular polynomial matrix over a field F, with
entry degrees at most d. Let S be any finite set of distinct points of F,
and let xi belong to an extension field. Then

    sum_(a in S) rank_F A(a)
      >= (|S|-d) rank A(xi).                       (4.1)

**Proof.** Put t=rank A(xi). For t=0 the assertion is immediate. Otherwise,
choose a t-by-t minor B(X) whose determinant is nonzero at xi. Its determinant
is a nonzero polynomial of degree at most td. At a sample a, the rank defect
t-rank B(a) is at most the multiplicity of the root a in det B: constant row
and column operations expose that many rows divisible by X-a. Summing those
multiplicities over the selected distinct points costs at most td. Hence

    sum_(a in S) rank B(a)>=t|S|-td.

Since rank A(a)>=rank B(a), this proves the claim. The proof never counts
unselected field elements. QED.

Apply the lemma to the emitted outer and inner interpolants. If
t0=rank_E Hglob, then

    sum_(zeta in O) rank_H J_zeta >= (R-d_out)t0,
    sum_(t in I) rank_F V_(zeta,t)
      >=(T-d_in)rank_H J_zeta.                     (4.2)

At a fixed site, each nonzero decoded tuple vector contributes one outer
product to V and costs at least d_code measured bits. This gives, for every
feasible measured table,

    W>=d_code (T-d_in)(R-d_out)t0
      =d_code T R t0/4.                            (4.3)

Since d_code>M/8, the coefficient is strictly greater than MTR/32 whenever
t0 is positive. No atomicity, source-validity or honest-support condition was
assumed in deriving (4.3).

## 5. Completeness and arbitrary-witness soundness

For an assignment x satisfying the source, use the predecessor's polynomials
f_j(X) representing beta_x^(s^j) and their inner power-basis representatives
g_(zeta,j)(U). At each selected pair (zeta,t), put the codeword G sigma(x) at
the one tuple u_j=g_(zeta,j)(t), and put zero at other tuples.

The honest inner and outer product polynomials have exactly the original
degree bounds. Their restrictions to I and O therefore interpolate back to
the same polynomials, by uniqueness. Every global moment is still

    m_(e,c)=beta_x^e sigma_c(x).

All emitted equations hold, and

    W_Y=TR wt(G sigma(x))<=MTR.                    (5.1)

Conversely, if an arbitrary feasible measured table had

    W<d_code K(T-d_in)(R-d_out),

then (4.3) would give rank Hglob<K. Apply the self-contained finite atomization
theorem in `VECTOR_HANKEL_ATOMICITY.md`, followed by the same coefficientwise
identifier and source decoding proved in Section 8 of the coded predecessor.
The mass equation forces a nonempty odd family of source-valid assignments.

Thus for an unsatisfiable source,

    W_NO>=d_code K(T-d_in)(R-d_out)>MTRK/32.        (5.2)

This proof starts from every word satisfying the new, explicitly emitted
affine system. It does not assume that the word is the restriction of any
feasible table from the old compiler.

## 6. Integer representatives, rank, and bit work

On the consistent affine branch choose a binary solution w0 and output

    Lambda={v in Z^D_trim:A_F(v mod2)=0}, target=w0.

The exact identity remains

    dist(w0,Lambda)^2=min{wt(w):A_F w=b_F}.

The proof compares parity weight with every integer residual and, conversely,
uses v=w0-w for every feasible binary w. The explicit full-rank basis has
entries in {0,1,2}. Set rho=ceil(sqrt(MTR)); then rho^2<=4MTR, so (5.2) gives
the strict norm ratio in (1.1). The inconsistent affine branch is sent to the
same rank-D_trim scaled strict-NO instance as in the predecessor.

Interpolation at arbitrary explicit distinct points uses polynomially many
field operations, for example by Vandermonde elimination. The number of
moments and constraints remains a fixed-degree polynomial in C,K,T,R,q,n
and the field bit dimensions. Dense emission and the full basis are counted
in the output work. At the preceding parameters T<=q and R<=Q, so this
refinement introduces no larger enumeration than the old compiler. The
new schedule's polynomial resource bounds are proved separately.

## 7. Exact same-parameter savings

Compare with the prior full grids, holding fixed the source, fields, code,
tuple domain and K. Directly from the coordinate counts,

    D_old/D_trim=Qq/(RT).                           (7.1)

For the old explicit rules q>=16hDelta and s^(h-1)>=N,

    T=2(h-1)Delta<2hDelta,
    R=2(n-1)Delta<2nDelta<32hNDelta,

because ell<4N and n=4h ell. Consequently

    q/T>8,
    Q/R>(16hDelta)^h/(32hNDelta)
       =(16hDelta)^(h-1)/(2N)
       >=[16h(2r+4)]^(h-1)/2.

Multiplication proves (1.4). For h=64,r=513,

    4[16h(2r+4)]^(h-1)
      =4(1054720)^63>10^380.                       (7.2)

Under the previous input-dependent schedule,

    h=Theta(sqrt(log N/log log N)), r=Theta_epsilon(h).

Thus the guaranteed rank reduction in (1.4) is

    2^Omega_epsilon(sqrt(log N log log N)).         (7.3)

The exact ratio can be larger. For fixed h,r this is an improvement in the
parameter-dependent constant; for growing h,r it is a subpolynomial
improvement in N. The leading inverse-deficit coefficient remains one.

## 8. Dependency and confidence record

The construction imports only proved components from the preceding packet:

- The explicit binary code and its left inverse: `CODED_CHANNELS_LEMMA.md`.
- The finite vector/matrix extraction theorem: `VECTOR_HANKEL_ATOMICITY.md`.
- The source packing, identifier collapse and exact integer handoff:
  `CODED_PACKED_TWO_LEVEL_FOLD.md`, Sections 3, 5, 8 and 9.

The only changed analytic step is the subset version of rank sampling, proved
in Section 4 above. Its use with a newly emitted affine system, both norm
bounds, all coordinate counts and the exact savings are proved here.

This improves the existing CVP-M10 construction. It does not introduce a new
source-soundness assumption or claim an improved leading coefficient below
one. The separate reconstruction-obstruction notes describe why certain
lossless channel-compression attempts fail; they are not hypotheses of this
positive theorem.
