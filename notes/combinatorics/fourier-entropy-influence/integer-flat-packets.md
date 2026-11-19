# Integer flat packets and bounded spectral spread

**Mira Cult · 16 November 2026**

Potapov's support-degree and support-weight argument extends to integer-valued
Fourier packets. Pairwise disjoint integer packets can then be summed
without losing their label entropy. This note includes the complete
support-weight argument and its bounded-spread determinant extension,
which provide the comparison point for the unrestricted-spread
[dyadic forest packets](spectral-conditioning.md).

The support-weight inequality and its determinant proof are credited to
Potapov [Pot26]; see [REFERENCES.md](REFERENCES.md).

[Overview](README.md) · [Catalogue](CATALOGUE.md) · [Verification](VERIFICATION.md)

All cubes carry the uniform measure. Fourier transforms are normalized by `2^(-n)`. All entropy logarithms in this note have base 2.

## 1. An unnormalized entropy for integer-valued functions

For a real function `g` on the `n`-cube define

    H_*(g)=sum_S ghat(S)^2 log_2(1/ghat(S)^2),
    I(g)=sum_S |S| ghat(S)^2.

No normalization of `g` is made. In particular `H_*` can be negative if some coefficient has magnitude greater than 1. It coincides with Fourier entropy for Boolean functions. Zero coefficients contribute zero; the zero function has both quantities zero.

**Theorem 1 (flat integer spectrum).** Suppose `g` is integer-valued and all its nonzero Fourier coefficients have the same absolute value `A`. Then

    H_*(g)<=4 I(g).                                      (1)

If `A<=1`, write `A=u 2^(-k)` with `u` a positive odd integer. Then `0<=k<=n`, and a more precise inequality is

    I(g)>= (k/2)||g||_2^2,
    H_*(g)<=4I(g)-2(log_2 u)||g||_2^2.                   (2)

If `g` takes values only in `{0,-1,1}` and is nonzero, then necessarily `u=1`: its nonzero Fourier magnitude is `2^(-k)` for an integer `0<=k<=n`.

### Proof of the arithmetic support bound

Let `D={s:ghat(s)!=0}` be the Fourier support, viewed as a subset of `{0,1}^n`, and let `1_D` be its Boolean indicator. Every Fourier coefficient of an integer-valued `g` is an integer multiple of `2^(-n)`, so the stated representation of `A` exists. If `A<=1`, `k` is nonnegative.

For `U subset [n]`, character orthogonality gives the exact face identity

    sum_{s subset U} ghat(s)
       =2^(|U|-n) sum_{x: x_i=1 for all i in U} g(x).    (3)

Here the sum on the right uses sign inputs, while the index `s` on the left is identified with a binary vector. Substitute `ghat(s)=u 2^(-k) epsilon_s`, where `epsilon_s` is `0`, `1` or `-1`. If `|U|>n-k`, (3) implies

    u sum_{s subset U} epsilon_s
       =2^(|U|-n+k) (an integer),

which is even. Since `u` is odd, the number of points of `D` in that lower face is even. These face parities are exactly the coefficients of the algebraic normal form over `F_2`. Consequently

    deg_F2(1_D)<=n-k.                                   (4)

The same argument is Potapov's support-degree argument for plateaued Boolean functions, with integrality of `g` replacing the stronger assumption that it takes only signs.

### The support-weight inequality, with proof

We use Potapov's inequality: for nonempty `D subset {0,1}^n` whose indicator has algebraic degree at most `d`,

    2 sum_{s in D}|s| >= |D|(n-d).                     (5)

For completeness, form the matrix over `F_2`

    M_{uv}=1[u subset v],  u,v in D.

After ordering `D` by nondecreasing Hamming weight, `M` is upper triangular with diagonal 1. Hence `det(M M^T)=1`. The entry `(M M^T)_{uv}` is the parity of the support of `1_D` on the upper face fixing the coordinates in `u union v` to 1. If this face has dimension greater than `d`, that parity is zero, since the restriction has algebraic degree below its dimension. The nonzero determinant supplies a permutation `pi` of `D` with all entries `(M M^T)_{u,pi(u)}` nonzero. Thus

    |u union pi(u)|>=n-d.

Summing `|u|+|pi(u)|>=|u union pi(u)|` gives (5).

Applying (5) with (4), and using flatness, yields

    I(g)=A^2 sum_{s in D}|s|
         >=(k/2) A^2|D|=(k/2)||g||_2^2.

Also

    H_*(g)=||g||_2^2 log_2(1/A^2)
          =2(k-log_2 u)||g||_2^2,

which proves (2). If `A>1`, all nonzero entropy summands are negative, so (1) is immediate.

Finally, Fourier inversion gives

    2^k g(x)=u sum_{s in D} epsilon_s chi_s(x).

For integer `g`, coprimality of `u` and `2^k` shows that `u` divides every value of `g`. A nonzero `{0,-1,1}`-valued `g` therefore has `u=1`. Its Fourier coefficients have magnitude at most `E|g|<=1`, completing the last assertion. ∎

## 2. A mixed-amplitude FEI theorem

**Theorem 2 (integer flat packets).** Let `f` be Boolean. Suppose

    f=sum_{a in A} h_a,

where each `h_a` is integer-valued with a flat nonzero Fourier magnitude, and the Fourier supports of the `h_a` are pairwise disjoint. Magnitudes are allowed to differ between packets. Then

    H(f)<=4 I(f).                                       (6)

Indeed disjoint Fourier supports imply the exact equalities

    H(f)=sum_a H_*(h_a),   I(f)=sum_a I(h_a),

and Theorem 1 can be summed.

There is useful rigidity hidden in the hypotheses: the functions `h_a` necessarily form a signed physical partition. Pointwise, their integer values sum to a sign, so `sum_a h_a(x)^2>=1`. Spectral orthogonality and Parseval give

    E sum_a h_a(x)^2=sum_a ||h_a||_2^2=||f||_2^2=1.

Thus equality holds at every input. Exactly one `h_a(x)` is nonzero there, and that value is `f(x)` in `{−1,1}`. In particular the theorem does not accidentally permit arbitrary signed cancellation among physical packets.

### 2.1 A common extension: bounded spread inside each packet

Flatness can be relaxed to a bounded ratio of nonzero amplitudes inside each packet. The absolute amplitudes of different packets may be arbitrarily different.

**Theorem 3 (integer packets of bounded spread).** Let `f` be Boolean and write `f=sum_a h_a`, where the `h_a` are integer-valued and have pairwise disjoint Fourier supports. If, for every nonzero packet,

    max_{S:hhat_a(S)!=0}|hhat_a(S)|
       <=R min_{S:hhat_a(S)!=0}|hhat_a(S)|,

then

    H(f)<=4R^2 I(f).                                   (6a)

This includes the flat-packet theorem at `R=1` and the bounded-spread theorem for a single Boolean spectrum. As above, the packet assumptions automatically imply a signed physical partition.

Here is the complete determinant argument underlying this extension. Let `g` be integer-valued, let `D` be its nonzero Fourier support, and set `a_S=ghat(S)`. The rational 2-adic valuation is denoted by `v_2`, normalized by `v_2(2)=1`; put `k_S=-v_2(a_S)`. Form the incidence matrix `M_{UV}=1[U subset V]` on `D` and

    K=M diag(a_S) M^T.

Its determinant is `prod_{S in D}a_S`, since `det M=1`. Its entries satisfy

    K_{UV}=sum_{W containing U union V}a_W
          =(D_{U union V}g)(1),

where the iterated discrete derivative is the average of `2^|U union V|` integer signed values. Therefore `v_2(K_{UV})>=-|U union V|`. The valuation of a sum is at least the minimum valuation of its summands; applying this to the nonzero determinant expansion gives

    sum_{S in D} k_S
      <=max_pi sum_{S in D}|S union pi(S)|
      <=2 sum_{S in D}|S|.                             (6b)

Since each `a_S=2^(-k_S)u_S` for an odd integer `u_S`,

    sum_{S in D} log_2(1/a_S^2)<=4 sum_{S in D}|S|.     (6c)

To turn this unweighted bound into entropy for a packet with comparable amplitudes, let `N=|D|`, `E=||g||_2^2`, and `alpha=min_D |a_S|`. Opposite ordering of positive numbers `p_S=a_S^2` and `log(1/p_S)` gives

    H_*(g)/E<=N^(-1)sum_{S in D}log_2(1/p_S).

One proof sums `(p_S-p_T)(log(1/p_S)-log(1/p_T))<=0` over all ordered pairs. This argument permits negative logarithms as well. Combining with (6c),

    H_*(g)<=[4E/N]sum_{S in D}|S|
           <=[4E/(N alpha^2)] I(g)
           <=4R^2 I(g),                               (6d)

where the last step uses `E<=N R^2 alpha^2`. Sum (6d) over the disjoint packets to prove (6a).

The unweighted-to-weighted loss is now explicit: it is the relative spectral spread *inside a packet*. The theorem allows unbounded differences between packets' absolute scales because they are separate integer-valued objects. For a general Boolean function the equal-magnitude Fourier layers need not have integer-valued inverses, so this does not eliminate the original FEI gap.
