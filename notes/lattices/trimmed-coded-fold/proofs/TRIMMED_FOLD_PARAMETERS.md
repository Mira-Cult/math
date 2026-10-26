# CVP-M10: optimized parameters for the trimmed coded fold

Date: October 11, 2026.  
Claim status: complete parameter proof, using the fully specified construction
in `TRIMMED_CODED_FOLD.md`. No new source-soundness, selector, or atomization
hypothesis is introduced. Independent model-assisted review is recorded
separately; this note is not a formal verification or external expert review.  
Registry impact: quantitative refinement of CVP-M10, not a new construction lane.

## 1. Finite construction and target

All logarithms in this note are base two. Fix a rational
`0 < epsilon < 1/2` and write `lambda=1-2epsilon=A/B` in lowest terms.
The source-size parameter satisfies `N>=8` and bounds its variables, equations,
and distinct monomials, with `R_src<N`. Let `ell` be the least power of two at
least `2N`. For powers of two `h>=2`, `q`, and `s>=2`, and an integer `r>=1`, put

    n=4h ell,       C=16h ell log q,
    Delta=(2r+4)s,  K=s^r,
    d_in=(h-1)Delta, d_out=(n-1)Delta,
    T=2d_in,        R=2d_out.

Here `T,R` denote the inner and outer sample counts, not moment-window lengths.
The trimmed compiler needs the finite field-size inequalities

    T<=q, R<=q^h, and R_src<q^h.                         (1.1)

Its explicit local binary code has `C<=M<=32C` and distance `d_code>M/8`.
The measured table and the full lattice rank have exactly

    D=MRTq^r                                                (1.2)

coordinates. Completeness gives squared distance at most `MRT`. Soundness
for every feasible binary word gives squared distance strictly greater than
`MKRT/32`. The parity-lattice identity extends these statements to every
integer representative. Therefore the integer YES radius

    rho=ceil(sqrt(MRT))

has a NO/YES ratio strictly greater than `sqrt(K/128)`. The exact sufficient
condition for the requested `D^(1/2-epsilon)` factor is

    K>128 D^lambda.                                      (1.3)

The parameter algorithm below verifies a stronger version of (1.3) using a
computable upper bound on `D`. The old sufficient condition
`s^(h-1)>=N` is unnecessary here: (1.1) is verified directly. The field
extensions still all have power-of-two relative degrees, so the explicit
quadratic-tower construction from the coded-fold packet applies unchanged.

## 2. Exact, bounded parameter algorithm

Define

    L=ceil(log N),
    G=bit_length(L),
    W=bit_length(max(1,floor(L/G))),
    r=max(2, ceil(4lambda/epsilon),
            ceil(sqrt(2lambda L/(epsilon W)))).          (2.1)

Square-root rounding in (2.1) is an integer comparison: choose the least
integer `z>=0` whose square is at least the indicated rational number.
For each candidate integer `1<=k<=L`, define

    h(k)=least power of two >= max(2,ceil((L+4)/k)+1),
    b(k)=ceil(log(4(h(k)-1)(r+2))),
    q=2^k,  s=2^(k-b(k)).                                (2.2)

A candidate is invalid when `k<=b(k)`. Otherwise `s>=2`, and choose the first
candidate passing

    K>128 D_star^lambda,
    D_star=h(k) k 2^[2L+14+(r+2)k].                      (2.3)

No real arithmetic is needed. Put

    c=r(B-A)-2A.

Then the strict comparison in (2.3) is exactly

    c k >= 7B+A(2L+14)+rB b(k)
                  +bit_length((h(k)k)^A).               (2.4)

For clarity, the bit length on the right is the integer bit length of the
positive integer `(h(k)k)^A`. It is not a rounded floating-point logarithm.

This is a bounded search. It can be implemented by binary search, since its
acceptance predicate is monotone; Section 3 proves that fact. If no candidate
passes, decide the source directly and output a fixed correct YES/NO
instance. The fallback is needed at only finitely many input lengths for
each fixed epsilon, with an explicit cutoff given below. Its cost is
absorbed in the epsilon-dependent constant of the polynomial runtime.
Construct the fields and affine table only after selecting the parameters.

### Direct verification of the field and rank bounds

Since `ell=2^(L+1)`, the definition of `h` gives

    q^(h-1)>=2^(L+4)=8ell.

Writing `n=4h ell`, equations (2.2) give

    T=4(h-1)(r+2)s<=q,
    R=(n-1)T/(h-1)<4h ell q/(h-1)<=8ell q<=q^h.

Also `q^h>=8ell q>N>R_src`. Thus (1.1) holds. The channel bound gives

    D=MRTq^r
      <=32C (8ell q) q q^r
      =4096h ell^2 k q^(r+2)
      =h k 2^[2L+14+(r+2)k]=D_star.                     (2.5)

Some inequalities in (2.5) are strict, but only the weak upper bound is used.
Consequently every accepted parameter set has the exact promised gap, with
no unquantified asymptotic loss in the factor.

## 3. Search monotonicity and finite fallback

First, (2.4) follows by raising (2.3) to the `B`th power and collecting the
powers of two. For an integer `m` and a positive integer `u`, the strict
inequality `2^m>u` is equivalent to `m>=bit_length(u)`. This accounts for the
strict fencepost in (2.4).

As `k` increases, `h(k)` and `b(k)` are nonincreasing. Also

    h(k+1)(k+1)<=2h(k)k,

so the final bit-length term in (2.4) increases by at most `A` in one step.
The choice `r>=4lambda/epsilon=8A/(B-A)` gives `c>=6A`. Hence the left side
minus the right side of (2.4) increases by at least `5A>0` at every step.
Validity `k>b(k)` is monotone as well. Binary search therefore returns the
same first successful `k` as exhaustive search.

Here is a conservative computable cutoff. Let `L_0` be the least power of
two at least

    (256/epsilon)^4.                                    (3.1)

For every `L>=L_0`, the last candidate `k=L` passes. At this candidate,
`h=4` and `b=ceil(log(12(r+2)))`. From (2.1), using `W>=1`, one obtains

    2<=r<=2sqrt(L/epsilon),
    b<=7+(1/2)log L+(1/2)log(1/epsilon)                 (3.2)

throughout this range. To verify the first upper bound, bound the three
terms in the maximum separately, using `L>=16/epsilon`. The second follows
from `12(r+2)<=48sqrt(L/epsilon)` and rounding upward by at most one.

At `k=L`, the logarithm of the left side divided by the right side in (2.3)
is

    F(L)=(2epsilon r-4lambda)L-rb
                  -lambda(14+log(4L))-7.

Since `epsilon r>=4lambda` and `r>=2`,

    F(L)>=r[epsilon L-b-(21+log(4L))/r]
         >=r[epsilon L-19-log L-(1/2)log(1/epsilon)]
         >=epsilon r L/2>0.                            (3.3)

The last inequality holds for all `L>=L_0`. One elementary check is to write
`u=log(1/epsilon)`. At `L_0`, its subtracted expression is at most
`52+(9/2)u`, because `log L_0<=33+4u`; this is less than `epsilon L_0/2`.
For example, multiplication by epsilon bounds the former by `31`, using
`epsilon<=1/2` and `epsilon log(1/epsilon)<=1`, while the latter becomes at
least `2^31/epsilon^2`. The ratio of the subtracted expression to `L`
decreases beyond `L_0`. These estimates also give `b<L`, so the candidate is
valid. Every fallback therefore has source length below the computable
constant `2^L_0`.

The cutoff proves polynomial time; it is not a practical recommendation to
instantiate the reduction at that size.

## 4. Sharp size estimate

The following asymptotics hold for each fixed rational epsilon. Put

    A_epsilon=sqrt(2(1-2epsilon)/epsilon^3).

The selected lattice satisfies

    log D <= L/epsilon
      +A_epsilon sqrt[L(log L-log log L)]
      +O_epsilon(sqrt(L/log L)+log L).                  (4.1)

In particular,

    D <= N^(1/epsilon)
      2^[(A_epsilon+o_epsilon(1))
                         sqrt(log N log log N)].        (4.2)

The sharper expression (4.1) can equivalently be expanded as

    log D <= L/epsilon+A_epsilon sqrt(L log L)
      -(A_epsilon/2)sqrt(L/log L) log log L
      +O_epsilon(sqrt(L/log L)+log L).                  (4.3)

All iterated logarithms in (4.1) and (4.3) are used only for sufficiently
large `L`; the exact finite algorithm does not evaluate them.

### Proof of (4.1)

The integer definitions imply

    W=log L-log log L+O(1),
    r=sqrt(2lambda L/(epsilon W))+O_epsilon(1).          (4.4)

The two constant lower bounds on `r` cease to be active for sufficiently
large `L`. Define the real comparison point

    kappa_0=2lambda L/(2epsilon r-2lambda).

Every successful candidate has `k>kappa_0`, by discarding the nonnegative
`b` and constant terms from its strict gap comparison. Uniformly for all
integers `ceil(kappa_0)<=k<=L`, dyadic rounding gives

    h(k)<=2(L+4)/k+4,
    h(k)k<=8L,
    h(k)r<=(4+o_epsilon(1))L/W.

The last inequality follows on substituting `k>=kappa_0` and (4.4).
Consequently a constant `B_epsilon` exists such that, uniformly on this
whole range,

    b(k)<=log(L/W)+O_epsilon(1)<=W+B_epsilon.            (4.5)

This uniform bound is established before choosing a successful candidate;
its constants do not depend on that later choice.

For all sufficiently large `L`, the integer

    k_candidate=ceil([2lambda L+r(W+B_epsilon)
                          +lambda(17+log L)+8]
                       /(2epsilon r-2lambda))          (4.6)

lies between `ceil(kappa_0)` and `L`. It is of order
`sqrt(L log L)`, while (4.5) is of order `log L`, so it also satisfies
`k_candidate>b(k_candidate)`. Inserting (4.5) and `h(k)k<=8L` into the exact
logarithmic gap expression shows that (4.6) has margin at least one. The
selected `k` is no larger than (4.6).

Since `log(hk)=O(log L)`, substitution into (2.5) gives

    log D_star <= 2L
       +(r+2)[2lambda L+rW]/(2epsilon r-2lambda)
       +O_epsilon(r+log L).

Use `lambda/epsilon=1/epsilon-2`. Direct algebra and
`L/r^2=O_epsilon(W)` then give

    log D_star <= L/epsilon
       +(lambda/epsilon^2)L/r+(r/(2epsilon))W
       +O_epsilon(r+log L).                            (4.7)

The two explicit excess terms in (4.7) are minimized at
`r^2=(2lambda/epsilon)L/W`. Rounding that `r` upward by at most one changes
their sum by at most `O_epsilon(W)`. Thus (4.4) and (4.7) yield

    log D_star <= L/epsilon+A_epsilon sqrt(LW)
                  +O_epsilon(sqrt(L/log L)+log L).

Finally, replacing `W` by `log L-log log L` changes the square root by
`O(sqrt(L/log L))`. This proves (4.1). The replacement
`L=log N+O(1)` proves (4.2); Taylor expansion gives (4.3).

This argument explains why retaining dyadic extension degrees costs no
extra leading constant: a factor of two in `h` changes `b(k)` by only
`O(1)`. It therefore contributes at the smaller
`O_epsilon(sqrt(L/log L))` scale. Choosing `r` first also makes integer
rounding of `k` cost only `O(r)`, at that same smaller scale.

## 5. Strict finite improvement at the old parameters

The optimization above is additional to a direct, exact saving. Keep any
old coded-fold parameters with

    q>=16h Delta, s^(h-1)>=N, n=4h ell<16hN.

Keep the same code, `s,r,q,h`, and hence the same `K`. Replace the old full
sample sets by `T=2d_in` and `R=2d_out`. Then

    D_old/D_trim=q^(h+1)/(RT)
      >4[16h(2r+4)]^(h-1).                             (5.1)

Indeed `T<2h Delta`, `R<32hN Delta`, so `RT<64h^2 N Delta^2`.
Insert `q>=16h Delta` and then `s^(h-1)>=N` to obtain (5.1). Both
constructions certify a squared gap greater than `K/128`; reducing `D`
therefore preserves every previously certified exact `D^(1/2-epsilon)`
promise.

For the previously displayed fixed schedule `epsilon=1/10, h=64, r=513`,
the right side of (5.1) is

    4(1,054,720)^63 > 10^380.

This is a pointwise rank reduction, independent of asymptotic notation or
unknown constants in the code length. For the prior growing schedule
`h=Theta(sqrt(L/log L))` and `r=Theta_epsilon(h)`, the guaranteed saving is
at least `2^Omega_epsilon(sqrt(L log L))` at identical `K` and gap.

The new construction retains leading rank-degree coefficient `1/epsilon`.
Neither (4.1) nor (5.1) proves a coefficient below one, a polylogarithmic
overhead over `N^(1/epsilon)`, or a fixed polynomial reduction at the
square-root endpoint. The improvement is the removal of unnecessary
sample coordinates, together with the sharper uniform parameter schedule.

## 6. Uniform construction cost and quantifiers

At the selected parameters, the lower bound `k>kappa_0` and the candidate
upper bound show

    k=Theta_epsilon(sqrt(L log L)),
    r,h=Theta_epsilon(sqrt(L/log L)),
    hk=Theta_epsilon(L),
    log K=(1/epsilon-2)L+O_epsilon(sqrt(L log L)),
    log(q^r)=(1/epsilon-2)L+O_epsilon(sqrt(L log L)).

In particular `q=N^o(1)`, `q^h<=2^(2L+O_epsilon(sqrt(L log L)))`,
`R=O(Nq)`, and `T<=q`. An element of `E` has `4h ell k=O(NL)` binary
coordinates. Enumerating binary polynomials to construct `F_q`, building
the quadratic towers, finding power bases by linear algebra, and computing
source-coordinate maps all have polynomial cost in `N` for fixed epsilon.
The code construction is polynomial in `C=O(NL)`.

The compiler enumerates `RTq^r` sites, `O(CK^2)` scalar moment positions,
and polynomially many interpolation and source constraints per position.
Even straightforward dense representations use a fixed polynomial in
`N`, `q^h`, `q^r`, `K`, `C`, and `NL`. Binary Gaussian elimination and the
parity-lattice basis conversion also have polynomial bit complexity in
these explicit dimensions. Thus the complete bit cost is `N^O(1/epsilon)`;
no constant depending on the growing `h` or `r` is silently treated as
fixed. The search itself uses `O(log L)` exact predicate evaluations.

These are separate statements: (4.1) bounds lattice rank, whereas the
matrix area and runtime may have larger polynomial exponents. Each fixed
rational epsilon determines one deterministic polynomial-time reduction,
including the finite fallback. The exact arithmetic is stated for rational
epsilon. For an arbitrary real deficit, a fixed rational deficit below it
still supplies the usual fixed-margin hardness statement; that observation
alone does not assert the same sharp `1/epsilon+o(1)` size for an
uncomputable real parameter.

## 7. Exact arithmetic checker

`experiments/check_trimmed_fold_parameters.py` verifies the integer
comparison against direct powers, bounded binary search against exhaustive
search, the selected field/rank inequalities, conservative cutoff
candidates, and the pointwise saving (5.1). Its certificate also compares
the old full-grid schedule, trimming at the identical old parameters, and
the optimized trimmed schedule.

The large displayed `L` values are virtual logarithmic input sizes; no
enormous finite field, source formula, or lattice is instantiated. Displayed
rank degrees divide certified logarithmic rank bounds by `L` and therefore
refer to virtual power-of-two sizes `N=2^L`. The acceptance and field tests
depend only on `L`, as does the parameter algorithm. These checks audit
finite arithmetic; they do not replace the arbitrary-witness soundness
proof or the asymptotic proof above.

The recorded run passes 1,128 direct integer comparisons, 1,295 comparisons
of binary search with exhaustive search, 191,345 monotonic-margin steps,
345 direct field/rank/gap checks, 90 pointwise grid-saving checks, and 18
conservative cutoff cases. Reproduce it with

    python experiments/check_trimmed_fold_parameters.py \
      --output experiments/certificates/trimmed_fold_parameters.json

Certificate SHA-256:

    2b0284691b8e235177be8994e68c48efe44d4055a2b7da8d81a385da3a974e6a

For example, at virtual `L=2^20` and `epsilon=1/10`, the certified rank-degree
upper bounds are approximately `10.2072591782` for the old full grid,
`10.2044086456` after trimming at those identical old parameters, and
`10.1731920242` for the newly optimized trimmed schedule. These are displays
of the exact rational bounds in the certificate. Its independently bracketed
actual rank ratios use `C<=M<=32C`, and certify a ratio greater than
`2^35716` between the old full grid and the optimized trimmed construction.
The identical-parameter saving bound, in which `M` cancels exactly, is
recorded separately and exceeds `2^2796` for that example.
