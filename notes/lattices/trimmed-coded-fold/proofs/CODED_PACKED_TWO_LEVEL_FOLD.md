# Coded packed folding: inverse-deficit coefficient one

**Research lane:** CVP-M10 / SymmetricMultilinearFold  
**Aliases in this refinement:** PackedTwoLevelFold; CodedPackedTwoLevelFold  
**Date:** October 11, 2026  
**Predecessor:** `PACKED_TWO_LEVEL_FOLD.md`, PR #369  
**Status:** complete mathematical proof draft. Model-assisted review and exact
finite regression results are recorded separately. This is not a Lean
formalization or external expert review.

## 1. The improvement

The previous packed construction has a source-channel loss in its gap:
the honest witness pays for C binary channels, while the NO argument charges
one unit per rank. At a local table position, however, an entire C-vector
contributes a matrix of rank at most one. This note makes every nonzero local
vector pay a constant fraction of C by placing it in an explicit binary code.

For every fixed power of two h >= 2 and integer r >= 1, define

    p0 = (r+2h)/(h-1),
    c0 = r/(2(r+2h)).

There is a deterministic polynomial-time reduction from 3SAT to Euclidean
GapCVP of lattice rank

    D = O_{r,h}(N^p0 log N)

that proves hardness within D^c for every fixed 0 < c < c0. In particular,

    (1/2-c0) p0 = h/(h-1) = 1 + 1/(h-1).

For every fixed 0 < epsilon < 1/2 this gives the clean rank bound

    D = O_epsilon(N^(1/epsilon+1))

for D^(1/2-epsilon)-GapCVP. More precisely, for every additional fixed eta>0,

    D = O_{epsilon,eta}(N^(1/epsilon+eta)).

The leading inverse-deficit coefficient has therefore decreased from 3/2 to
1. A further uniform parameter schedule is proved separately in
`CODED_FOLD_UNIFORM_SCHEDULE.md`; it does not change the construction.

There is no assumed selector, low-cost atomicity, proper-image map, or source
soundness hypothesis. Sections 3--8 specify the emitted affine system and
derive soundness for every binary witness. Section 9 handles every integer
lattice representative. The common-atom fact is proved directly in
`VECTOR_HANKEL_ATOMICITY.md`, so this packet does not rely on the unavailable
external common-atom repository.

## 2. An explicit binary code and its exact use

For every C>=1, the companion `CODED_CHANNELS_LEMMA.md` constructs in
deterministic time polynomial in C an injective binary linear map

    G : F_2^C -> F_2^M,

with a binary left inverse R, such that

    C <= M <= 32C,
    d_code := min_{v!=0} wt(Gv) > M/8,
    R G = I_C.

Here is a self-contained description of the construction. Put

    m=ceil(log_2(2C)), k=ceil(C/m), q_code=2^m.

Zero-pad the input to km bits, regard it as k symbols of F_(q_code), and
evaluate the corresponding polynomial of degree <k at 2k distinct field
points. The resulting Reed--Solomon word has at least k+1 nonzero symbols
when the input is nonzero.

Encode each symbol v in F_2^m by the same binary linear inner code of length
8m. Its rows g_j are chosen greedily among all vectors in F_2^m to minimize

    U_j = sum_{v!=0} 2^(-wt_j(v)).

For a uniformly chosen next row, every nonzero v has parity zero or one with
equal probability. Thus the next-row average of U is (3/4)U, and a minimizing
row satisfies the same inequality. After 8m rows,

    sum_{v!=0} 2^(2m-wt(G_inner v))
      <= (2^m-1) 2^(2m) (3/4)^(8m)
      < (6561/8192)^m < 1.

Therefore every nonzero inner word has weight at least 2m+1. Concatenation
has length M=16km<=32C and distance at least (k+1)(2m+1)>M/8. All minimizations
enumerate at most q_code<4C rows and q_code-1 messages and use exact integer
arithmetic after clearing powers of two. Binary Gaussian elimination gives R.

The actual measured variables will be M-bit words w at each table site.
We emit the linear equations

    w = G R w,                                          (2.1)

and use z=Rw in every equation of the packed compiler. These z values are
derived linear forms, not additional witness coordinates. Equation (2.1)
ensures w=Gz, so w is zero exactly when z is zero. The lattice dimension
counts every one of the M measured bits; it is not reduced by counting only
the dimension of the binary code.

## 3. Source, fields, and packed semantics

### 3.1 Sparse quadratic source

Start with a 3CNF. For each clause, write a_1,a_2,a_3 for the Boolean indicators
that its literals are false. With one new Boolean variable y, impose

    y+a_1 a_2=0,  y a_3=0

over F_2. These equations are equivalent to satisfaction of that clause and
have degree at most two. The resulting sparse quadratic system g_j(x)=0 has
size linear in the input encoding length. Pad the size parameter N so that
N>=8 bounds the number of variables v, equations, and distinct quadratic
monomials R_src, with R_src<N. If R_src=0, decide the linear source directly.

### 3.2 Parameters and fields

Fix h a power of two with h>=2 and r>=1. Let s be the least power of two with
s^(h-1)>=N, and put

    K=s^r, L=4K, T=5K-1, Delta=(2r+4)s.

Let q be the least power of two >=16h Delta. Let ell be the least power of
two >=2N. Construct compatible field towers

    F=F_q < H=F_(q^h) < B=F_(q^(h ell)) < E=F_(q^(4h ell)).

Write n=[E:F]=4h ell and Q=|H|=q^h. Use the degree allowances

    d_in=(h-1)Delta, d_out=(n-1)Delta.

The choices give

    q >= 2 d_in, Q >= 2 d_out, Q > R_src.               (3.1)

Indeed n<16hN, N<=s^(h-1), and q>=16h(2r+4)s. Hence

    d_out <16hN(2r+4)s <=16h(2r+4)s^h <=q^h/2.

The inner inequality is immediate. None of these estimates requires r>=h;
the restriction in the predecessor served its old positive-gap exponent.

All fields and coordinate maps are deterministic and explicit. Enumerating
and testing binary polynomials of degree log_2(q) constructs F_q in time
polynomial in q. Subsequent relative extension degrees are powers of two.
Over each field, find a binary-basis element with absolute trace one and
adjoin a root of X^2+X+a. A trace-one element exists because absolute trace
is a nonzero linear map, and this quadratic is irreducible. Repeat to build
the tower. The last quadratic generator in a power-of-two relative extension
lies outside the unique maximal proper subfield and generates the entire
relative extension. Linear algebra gives compatible power bases.

Choose generators omega for H/F, Y for B/H, and eta_E for E/F, and choose
three B-independent elements theta_0,theta_1,theta_2 in E. For fixed h,r,
all field elements have O_{h,r}(N log N) bits. No enumeration of E is used.

### 3.3 One product for all source monomials

List the monomials x_(i_k)x_(j_k) and distinct points xi_k in H. Let A_x(Y)
and B_x(Y) be their interpolation polynomials of degree <R_src, with values
x_(i_k) and x_(j_k). Since ell>=2N>2R_src-2, their product in B has its ordinary
polynomial representative of degree <=2R_src-2. In particular,

    (A_x B_x)(xi_k)=x_(i_k)x_(j_k).                    (3.2)

Fix a binary-linear injection iota:F_2^v->B, a binary left inverse chi, and
I=im(iota). Put T_x=iota(x). There are computable binary-linear maps LA,LB:B->B
with LA(T_x)=A_x and LB(T_x)=B_x. Every source equation is represented by a
computable binary-linear map Gamma_j:B x B x F_2->H satisfying

    Gamma_j(T_x,A_x B_x,1)=g_j(x).                     (3.3)

Set

    beta_x=theta_0 T_x+theta_1 A_x+theta_2 B_x,
    v_x=(1,T_x,A_x,B_x), C_x=v_x v_x^T.

The map x->beta_x is injective. Fix a binary basis e_0=1,e_1,...,e_(b-1) of B,
where b=h ell log_2(q). Expand the 16 ordered entries of C_x in this basis,
giving a nonzero binary vector sigma(x) with

    C=16b=O_{r,h}(N log N)

channels. It is nonzero because C_x(0,0)=1.

All binary-linear source maps below act on these retained channel vectors.
They are not applied to an assembled E-valued moment: a binary-linear map on
B need not commute with multiplication by beta_x^e in E.

## 4. The complete measured affine compiler

At every site

    (zeta,t,u) in H x F x F^r

introduce an M-bit measured vector w_(zeta,t,u). Impose (2.1) there and define
the C derived bits z_(zeta,t,u)=R w_(zeta,t,u). Thus the total measured length
and the final full lattice rank are exactly

    D = M Q q q^r.                                    (4.1)

Represent a nonnegative exponent by its r-digit radix-s expansion, allowing
the top digit to be unbounded. Put

    phi_a(u)=product_j u_j^(dig(a)_j).

For 0<=a<K and 0<=b0<=L, write d(a,b0) for the sum of all digits of a and b0.
The elementary bound d(a,b0)<Delta holds for every r>=1; for r=1 the digit
sum is at most 5s-1<6s=Delta. Form the local matrices

    V_(zeta,t)((a,c),b0)
       =sum_u z_(zeta,t,u,c) phi_a(u) phi_b0(u).        (4.2)

Interpolate each entry as a function of t over all F, and emit the vanishing
of all coefficients above degree (h-1)d(a,b0). Call this polynomial
P_(zeta,a,b0,c)(U). Evaluate at omega to obtain J_(zeta,a,b0,c) in H.

Interpolate each J entry as a function of zeta over all H, and emit the
vanishing of all coefficients above degree (n-1)d(a,b0). Call the resulting
polynomial R_(a,b0,c)(X). Define

    Hglob((a,c),b0)=R_(a,b0,c)(eta_E).

For 0<=e<=T, choose a_e=min(e,K-1), b_e=e-a_e, and define m_(e,c) by the
corresponding Hglob entry. Emit every Hankel consistency equation

    Hglob((a,c),b0)=m_(a+b0,c).                        (4.3)

All of these are F_2-linear constraints on measured w. Polynomial coefficients,
moments, decoded bits, and interpolants are derived forms and create no
additional witness variables.

## 5. Frobenius, identifiers, and source equations

For every 0<=e<K and every channel c, emit

    m_(2e,c)=m_(e,c)^2.                               (5.1)

Regroup c as (i,j,k) with 0<=i,j<4 and 0<=k<b, and abbreviate

    S_e(i,j)=sum_k e_k m_(e,i,j,k).

For every 0<=e<K emit:

1. channelwise symmetry between (i,j,k) and (j,i,k);
2. m_(e,0,0,k)=0 for k>0;
3. for every j=0,1,2,3,

       S_(e+1)(0,j)=theta_0 S_e(1,j)
                    +theta_1 S_e(2,j)+theta_2 S_e(3,j); (5.2)

4. the binary-matrix channel equations T in I, A=LA(T), Bv=LB(T), using the
   channel vectors at (0,1),(0,2),(0,3);
5. the binary-matrix channel equations Gamma_j(T,P,mass)=0, using the vectors
   at (0,1),(2,3) and the single surviving mass channel.

Finally emit

    m_(0,0,0,0)=1.                                    (5.3)

Every E-valued equation is expanded in a fixed binary basis. Squaring in E
is F_2-linear. The result is an explicit ordinary binary affine system

    A_F w = b_F.

## 6. Completeness

Suppose x satisfies the source. For j=0,...,r-1 let f_j(X) in F[X], of degree
<n, represent beta_x^(s^j) in the eta_E power basis. For each zeta in H, let
g_(zeta,j)(U) in F[U], of degree <h, represent f_j(zeta) in the omega basis.

At each (zeta,t), choose exactly one tuple

    u_j=g_(zeta,j)(t).

Write w=G sigma(x) there and zero at every other u. Decoding gives precisely
the honest table of the predecessor. Its inner interpolant is

    sigma_c(x) product_j g_(zeta,j)(U)^(dig(a)_j+dig(b0)_j).

The outer interpolant is the analogous product of the f_j(X), and its final
value is sigma_c(x) beta_x^(a+b0). The two degree constraints hold by their
definitions. Frobenius holds because sigma_c(x) is binary. The packed source,
identifier, symmetry and mass equations follow from Section 3.

The exact honest weight is

    W_Y=Qq wt(G sigma(x)) <= M Qq.                    (6.1)

The compiler does not compute an assignment; the assignment is used only to
prove existence of an honest feasible witness.

## 7. A stronger all-witness rank charge

### 7.1 Polynomial-matrix sampling

Let A(X) be a rectangular polynomial matrix over a finite field of size q,
with all entry degrees <=d. For an extension-field point xi, write
t=rank A(xi). Then

    sum_{a in F_q} rank A(a) >= t(q-d).              (7.1)

Choose a t-by-t minor with determinant nonzero at xi. Its determinant has
degree <=td. At each a, if the minor loses j ranks, constant row/column
operations expose j rows divisible by X-a, so its determinant vanishes to
order at least j. The sum of these orders is at most td. Summing rank defects
proves (7.1), including rectangular matrices. Rank zero is immediate.

Apply (7.1) to the emitted outer interpolants and then to each inner
interpolant. If t0=rank_E(Hglob), this gives

    sum_zeta rank_H J_zeta >= (Q-d_out)t0,
    sum_t rank_F V_(zeta,t) >= (q-d_in)rank_H J_zeta.  (7.2)

### 7.2 Charge a whole vector once

For any fixed local table, the summand of (4.2) indexed by u is

    (phi_a(u) z_(u,c))_((a,c)) (phi_b0(u))_(b0)^T.

This is an outer product, hence has rank at most one regardless of how many
channels are nonzero. Consequently, for every feasible local coded table,

    rank_F V <= number of nonzero z_u
             = number of nonzero w_u
             <= (sum_u wt(w_u))/d_code.              (7.3)

No honest-table, positivity, sparsity, or atomicity promise was used.
Combining (7.2) and (7.3) yields the exact new inequality

    W >= d_code (q-d_in)(Q-d_out) rank_E(Hglob).       (7.4)

In particular, since d_code>M/8 and (3.1) holds,

    W >= (M Qq/32) rank_E(Hglob),                    (7.5)

with strict inequality when the rank is nonzero if the exact code-distance
bound is used. This is the improvement over the predecessor's charge of
only Qq/4 per rank.

## 8. From low rank to an actual satisfying assignment

Suppose

    W < d_code K(q-d_in)(Q-d_out).

Equation (7.4) gives t0=rank Hglob<K. The self-contained vector-Hankel theorem
in `VECTOR_HANKEL_ATOMICITY.md` applies to m_e with K row blocks and 4K+1
columns and the emitted identities (5.1). It supplies distinct beta_l and
nonzero binary coefficient vectors sigma_l, with u<=t0<K, such that

    m_(e,c)=sum_{l=1}^u beta_l^e sigma_(l,c), 0<=e<=K. (8.1)

The proof is a finite linear-algebra argument: a row-rank plateau makes shift
well-defined on a finite state space; its recurrence extends Frobenius;
Frobenius makes the common annihilator ideal radical; splitting its squarefree
generator gives (8.1). It does not assume that any original w or z table is
already a population of assignment atoms.

Regroup each sigma_l into a 4-by-4 matrix C_l over B. It is nonzero because
binary basis expansion is injective. Vandermonde isolation using e=0,...,u-1
turns the emitted equations into coefficientwise identities. They imply
symmetry, C_l(0,0) in F_2, and

    beta_l C_l(0,j)=sum_{i=0}^2 theta_i C_l(i+1,j).     (8.2)

If C_l(0,0)=0, (8.2) for j=0 and B-independence of the theta_i annihilate the
first column. Symmetry annihilates the first row. The other identities then
annihilate every column, contradicting C_l!=0. Thus C_l(0,0)=1.

Let T_l=C_l(0,1), A_l=C_l(0,2), B_l=C_l(0,3). The first column gives

    beta_l=theta_0 T_l+theta_1 A_l+theta_2 B_l in E.

The other columns and independence of the theta_i now give

    C_l=(1,T_l,A_l,B_l)(1,T_l,A_l,B_l)^T.              (8.3)

The channelwise equations imply T_l in I, A_l=LA(T_l), B_l=LB(T_l), and
Gamma_j(T_l,A_l B_l,1)=0. Thus x_l=chi(T_l) is a Boolean assignment satisfying
every source equation. Finally (5.3) says

    1=sum_l C_l(0,0)=u mod 2,

so at least one such assignment exists. Contrapositively, UNSAT gives

    W_NO >= d_code K(q-d_in)(Q-d_out)
          > M Qq K/32.                               (8.4)

This completes arbitrary-binary-witness soundness, with source semantics
derived from the emitted equations rather than assumed as an interface.

## 9. Exact Euclidean handoff

First test consistency of A_F w=b_F. On the consistent branch find a binary
solution w0 and output target w0 and the full-rank lattice

    Lambda={v in Z^D : A_F(v mod 2)=0}.

For every integer v in Lambda, w0-v reduces to a feasible binary word. Each
odd integer coordinate contributes at least one to squared Euclidean norm,
so wt((w0-v) mod 2)<=||w0-v||_2^2. Conversely, for every feasible binary w,
the integer vector v=w0-w belongs to Lambda and has ||w0-v||_2^2=wt(w).
Therefore

    dist(w0,Lambda)^2=min{wt(w): A_F w=b_F}.           (9.1)

An explicit lattice basis is obtained from binary row reduction. If I are
pivot coordinates and J free coordinates and the homogeneous equations read
v_I=B0 v_J mod 2, use columns 2e_i for i in I and
e_j+sum_i (B0)_(ij)e_i for j in J. These D independent integer columns generate
Lambda and have entries in {0,1,2}. The target has entries in {0,1}.

Set the integer YES radius rho=ceil(sqrt(MQq)). It satisfies rho^2<=4MQq.
Equations (6.1) and (8.4) show a gap strictly exceeding

    sqrt(K/128).                                     (9.2)

The inconsistent affine branch cannot occur for a satisfiable source. It
can be mapped to the rank-D lattice 2A Z^D with target A e_1, where
A=(D+1)rho. Its distance is A>D^(1/2-epsilon)rho for every epsilon in (0,1/2).
This is an explicit strict-NO fallback with polynomial bit length.

## 10. Fixed-parameter resource ledger and schedules

For fixed h,r, let delta=1/(h-1). Then

    s=Theta(N^delta), q=Theta_{r,h}(N^delta),
    K=Theta_r(N^(r delta)),
    Qq=Theta_{r,h}(N^(1+2delta)),
    C=Theta_{r,h}(N log N), M=Theta_{r,h}(N log N).

Consequently,

    D=O_{r,h}(N^(r delta+2+2delta) log N),
    W_Y=O_{r,h}(N^(2+2delta) log N),
    W_NO=Omega_{r,h}(N^(r delta+2+2delta) log N),
    gap=Omega_{r,h}(N^(r delta/2)).                   (10.1)

The common log factor cancels from the radius ratio; it remains in D.
For every c<c0=r/[2(r+2h)], the positive exponent slack ensures gap>D^c for
all sufficiently large sources. Finitely many smaller lengths can be handled
separately for each fixed parameter choice. This gives the theorem in
Section 1 with p0=(r+2h)/(h-1).

For a target epsilon in (0,1/2), choose

    h = least power of two >=1+4/epsilon,
    r = floor(h/epsilon-2h)+1.                       (10.2)

Then r>=1 and c0>1/2-epsilon. The construction remains valid when r<h.
Moreover,

    p0 <= 1/epsilon + (1/epsilon+1)/(h-1)
       <= 1/epsilon + 1/4 + epsilon/4
       < 1/epsilon + 3/8.

Absorbing log N gives D=O_epsilon(N^(1/epsilon+1)). For any prescribed eta>0,
instead choose a power of two h with

    h-1 >= 2(1/epsilon+1)/eta

and use the same strict r schedule. Then p0<=1/epsilon+eta/2 and the log
factor is absorbed in the remaining eta/2, proving the sharper statement.

### Running time is counted separately

Lattice rank is not the binary matrix area or runtime. There are O(CK^2)
scalar moment positions; degree equations can be emitted by interpolation
and binary expansion with polynomial overhead in C,K,Q,q,n. Each derived
form is a linear combination of D measured variables. Even dense matrix
emission, binary elimination, and a D-by-D output basis take polynomial time
in these quantities. Their source-size exponents are O(r/(h-1)+1), and hence
O(1/epsilon) under (10.2). The exact displayed coefficient one refers to
lattice-rank degree, not the runtime exponent or dense output bit count.

## 11. What this result does and does not establish

The new positive theorem is the code-amplified rank bound (7.4) combined with
the unchanged, fully specified source compiler. The separate self-contained
atomization proof removes an opaque dependency and also applies to the
predecessor's vector window.

For comparison, the clean rank-degree schedules for epsilon=1/10,1/100,1/1000
are now 11,101,1001, compared with 16,151,1501 in the preceding packed note
and 55,505,5005 in the original multilinear-fold schedule. These are
asymptotic polynomial degrees; constants depending on epsilon can be large.

This does not prove a sqrt(D)/polylog(D) reduction of fixed polynomial degree,
and it does not attain a coefficient 1/2 in front of 1/epsilon. The concrete
remaining product overhead is the C semantic channels times the Qq scalar
samples. A sampler lower bound for this separated architecture, together with
the optional growing-parameter schedule, is recorded in
`CODED_FOLD_UNIFORM_SCHEDULE.md`. That bound is scoped to this architecture.

## 12. Verification and dependency map

The full mathematical dependencies are local and proved:

- explicit concatenated binary code: `CODED_CHANNELS_LEMMA.md`;
- vector/matrix common atoms: `VECTOR_HANKEL_ATOMICITY.md`;
- source packing and rank-one decoding: Sections 3 and 8 above;
- polynomial rank sampling: Section 7.1 above;
- parity-kernel geometry: Section 9 above.

The executable `experiments/check_coded_channels.py` constructs small exact
codes, checks their distance and linear maps, tests local vector-rank charging,
and verifies rational parameter schedules. Its certificate is
`experiments/certificates/coded_channels.json`. The predecessor's
`experiments/check_packed_two_level_fold.py` independently retains the
two-level rank-sampling, packed identifier, interpolation, and atomic-source
regressions. Additional atomicity and uniform-schedule checks are documented
in their companion notes.

Finite tests support implementation and boundary checks; they are not a
formal verification of the asymptotic compiler or a replacement for this
proof. Review notes state exactly which mathematical steps were independently
checked. No accepted theorem status on main is silently changed.
