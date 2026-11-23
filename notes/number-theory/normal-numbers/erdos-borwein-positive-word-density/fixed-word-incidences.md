# Positive lower density of every fixed binary word of Erdős–Borwein

Using the independently audited [certified-incidence isolation proof](conditional-isolation.md), for any fixed a>7/12 and each fixed binary word w of length k and value u, there is c(a,w)>0 such that, for all sufficiently large N and N^a≤H≤N, at least c(a,w)H copies of w occur wholly in the H physical binary places of E after N. This is positive ordinary lower density for every fixed word, with neither equal frequencies nor normality. There is no uniform growing-k assertion.

Choose a fixed anchor A0=2^(2u), and cofactors b=A0m≤N^θ with m odd squarefree, where θ is a sufficiently small fixed a-dependent constant as before. Put j0=ω(m)+k+1. Each actual prime p in the corresponding physical affine interval yields n=bp−j0. Since p>b, its actual divisor coefficient is

    d(n+j0)/2^(j0+1) = (2u+1)/2^(k+1),

the exact midpoint of w's cylinder. This includes the all-zero and all-one words. For primes no congruence class is imposed beyond the admissible interval. The marker remains a genuine actual coefficient; it does not replace any part of the complementary phase.

The reciprocal asymptotic Σ_{m≤x, odd squarefree}1/m=[2/(3ζ(2))]log x+O(1), obtained by expanding μ² and excluding prime 2, and the uniform short-prime count give

    λ=E_n F ~ [2/(3ζ(2) A0)] log(1/(1−θ)).

As before the restriction j0≤CT loses o(1) of ambient incidence mass by a fixed exponential Ω weight. Boundary trimming H−k+1 gives the same λ and probability up to o(1): apply the argument with any fixed a' in (7/12,a) for large N.

For a distinct-offset collision m=g0m', m2=g0m2', we must have A0g0 dividing the nonzero D=ω(m')−ω(m2'). The prime pair lies on two primitive-slope linear forms with parameter interval length H g0/(A0 m m2)+O(1). The singular factor for D/(A0g0) is at most that for D/g0. Dropping A0 from the divisibility restriction only enlarges the count, so the previous two-form Selberg bound and harmonic-model modular calculation give E F(F−1)≪_a θ²/A0 for fixed A0 and sufficiently large N. Uniformity of the sieve exponent uses θ≤θ0<a/4, so the parameter length exceeds N^(a/2) up to constants for large N. Consequently E F²≪_a θ/A0. The constants for sufficiently large N can depend on the word.

In the complementary incidence proof, gcd(b,j−j0) satisfies Ω≤Ω(A0)+Ω(gcd(m,j−j0)); treat the former as a fixed explicit constant. The latent gcd expansion and stride sum over j apply before averaging m, as before, and the common factor 1/A0 cancels in the normalized incidence measure. The marked positive majorant is now bounded after averaging by O_a((1+Ω(A0))²+log²(W+2)); the old integrated outer estimate may use a constant depending on A0. Other bank and modulus estimates depend only on b≤N^θ and still hold. Thus the same avoidance event probability ≥e^-4W is available, and conditional mean complementary chord can be made less than any fixed aperture by enlarging W. In particular use d_k/2, where d_k=2sin(π/2^(k+1)) is the distance of the selected midpoint to the two cylinder endpoints on the unit circle. Take W sufficiently large so the conditional upper C_a[(1+Ω(A0))²+log²(W+2)]/W and outer exponentially small terms beat that aperture. Then EF_good≫λ e^-4W, and Cauchy–Schwarz gives an ordinary density lower bound ≫_a (θ/A0)e^-8W. This is far smaller than the normal benchmark 2^-k (already A0=2^(2u), and W must pay the 2^-k-scale aperture). It gives no upper frequency law, and no claim that this sufficient lower constant is optimal. All comparisons are for each fixed w with all constants chosen before N.

## The outside of the central deficit strip

In the central sector |B_j|>B* one does not need a W-uniform bank envelope. Use the fixed-order all-atom arithmetic comparison at one coordinate, with max comparator atom O(T^-1/2) for the positive mark; sum over the O(L sqrt T) central sites. The adaptive gcd average yields E_I Σ_j z_j/sqrt(T)≪_a L log²(W+2), or the same with the fixed anchor constant included. Summing reciprocal-square weights gives O_a(L log²(W+2)/B*)+o(1). Set L=e^(20W), B*=e^(50W), so this is exponentially below the avoidance probability. Enlarging the fixed B* adds no relative term in the marked sector since its s-weights are summable; additive errors times the fixed finite count still vanish as N grows. On each p interval p≍X, converting the positive marked averages from normalized log-prime weights to ordinary prime weights changes them by a factor 1+O(1/log X), uniformly in b, including for nonnegative unbounded force sums.

See [verification and source notes](VERIFICATION.md) for review scope. The previous [fixed-word prefix result](https://github.com/CaptainSude/erdos-borwein-disjunctivity/releases/tag/v1.0.0) gave a vanishing lower bound on the proportion.

[Back to the theorem](../0002-erdos-borwein-positive-word-density.md).
