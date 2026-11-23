# Integrated actual fixed-deficit approximation over all O(T) shifts

On the b=1 whole prime shells of the two-site theorem, uniformly over all allowed shifts 1≤j≤C_0T and integer targets |v|≤C T,

    Pr(V_j=v, R_j≥r)
       ≪ [1/(√t (1+r²))] [1+(v−t)²/t]^-1,       r≥0,

where R_j is the total repeated multiplicity of Ap+j. Consequently, for any shell- or row-selected subset I of these shifts and fixed h≠0,

    E Σ_(j∈I, D_j>M) |e(h d(Ap+j)/2^(K+1+j))−1| ≪_h (1+M)^-1.

This pays the entire actual transition band (indeed all O(T) shifts), not a central restriction. Pruning to actual deficits 1..M changes the signed product in L¹ by O_h(1/M), even with an arbitrary bounded original-row multiplier. The usual real far-tail reduction then applies separately to the shifts beyond C_0T.

**Weighted atom envelope.** Put f(a)=(1+(a−t)²/t)^-1. In the geometric-bank recursion retain a relative atom error ε_i h f(a)/√t plus exponential additive error instead of ε_i h/√t. All model atoms through stage i are O(f(a)/√t), including after up to four forced successes. To see it, split the first bank model into two sets of comparable variance (greedily splitting its independent Bernoulli trials); each has maximum atom O(1/√t) by Fourier inversion. Add all later banks to one side; its maximum atom does not increase and both centered variances are O(t). Their total mean differs from t by O(log T)=o(√t), uniformly in j. On a sum event at distance ≥2√t from the mean, at least one side lies at distance at least half that distance from its own mean. Chebyshev on that side and the maximum atom on the other bounds the sum atom by O(f(a)/√t). Bounded forced successes do not affect these arguments.

For the first-bank BV/Taylor comparison the additive error is exponentially small, uniformly in the exact atom; it may be left additive. For later banks the [geometric-share weighted recursion](valuation-atom-bound.md) is unchanged except for f(a−b)≤2(1+b²/t)f(a), obtained from the triangle inequality for distances to t. In the interior b<r_i this ratio costs O(1) for every i≥2 since r_i=O(log T). In the exterior the exact atom is paid by the endpoint moment divided by binom(b,r_i), as before, and

    Σ_(b≥r) (1+b²/t)/binom(b,r) = O(1+r²/t)  for r≥5.

For example the beta-integral identity gives E-like sums Σ_(b≥r) (b−r)(b−r−1)/binom(b,r)=4r/[(r−1)(r−2)(r−3)] and the corresponding degree 0 and 1 sums by geometric differentiation. Consequently the same recursive choice of degrees gives bounded ε_i and exponential additive errors. The proof works also with nonnegative weights from up to four forced supplementary tests, using the unchanged O((log P)^4) multiplicity and modulus exponent <.19. When a forced prime overlaps a bank it changes at most four Bernoulli trials into deterministic successes; the same envelope and the endpoint mean bound with +4 apply. Weighted error bounds can be summed at comparator level over the forced test weights; absolute BV costs are paid collectively as in the preceding geometric-share argument. All variables and bank atom supports have size O(log P), but the exponential additive errors are used only in finite interior inversions or reciprocal-binomial sums, not multiplied by this support size.

As in the central truncation note this yields

    E[1(U=a)(1+(V_j−U−c)^2)(1+R_j²)]
        ≪ f(a)/√t + exp(−κt)

uniformly, by upper prime and repeated-power moments with ≤4 tests. Omitted fourth moment tails decay faster than exp(−κt), using the same squared-divisor shell and last-power cutoff estimates. The bounded c is the geometric terminal center. Divide by (1+(v−a−c)²)(1+r²) and sum over a. The convolution bound Σ_a f(a)/(1+(v−a−c)²)≪f(v) follows by splitting where |v−a−c|≤|v−t|/2 and its complement: in the first range f(a)≪f(v) when |v−t|≫√t, whereas in the second the kernel is O((v−t)^-2) and Σ f(a)≪√t; near the center use the kernel sum. This initially leaves exp(−κt)/(1+r²), which is negligible relative to f(v)/√t for targets |v|≤C T, and this is the only range needed below. Outside it retain the additive exponential error; the leading displayed uniform bound is intended for |v|≤C T.

**Summed consequence.** For each deficit b>M the target is v=K+1+j−b. If it is negative the event is empty; otherwise both j,b are O(T) there. Uniformly in b, Σ_(1≤j≤C_0T) f(K+1+j−b)/√t≪1, just by summing the integer translates of the envelope. When R_j<b/4 we have |z_j−1|≤2π|h|2^(-b/2) from log₂ odd(d)≤2R_j; otherwise use |z_j−1|≤2 and the power-tail joint atom. Sum in b to obtain the claimed O_h(1/M). Pointwise product telescoping proves the signed L¹ conclusion. This does not estimate the remaining finite-deficit signed phase itself or establish its independence from original record events. Private only.

[Back to the theorem](../0002-erdos-borwein-positive-word-density.md).
