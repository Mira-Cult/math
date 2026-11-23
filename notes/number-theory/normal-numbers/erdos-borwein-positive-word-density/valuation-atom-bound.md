# Reversed geometric modulus shares give the optimal-order true atom upper bound

Use actual harmonic prime shells p∈(P/2,P], n=Ap, t=loglog P≥T^(3/4)+O(1), T=loglog N, with A≤P^ε, from the prior C_K disintegration. Write V_j=v₂(d(Ap+j)). Let L_0=T, L_i=log L_(i−1), and choose d maximal with L_(d−1)≥H, H a fixed sufficiently large absolute constant. Then H≤L_(d−1)<exp H; d≤log* T grows. Work in the coprime form (A/g)p+j/g, g=gcd(A,j), using only eligible reduced residue classes. Fix a square-factor cutoff b≤B_0, where B_0 is an arbitrary sufficiently large fixed constant; this costs O(1/B_0) of the global harmonic core mass (not o(1) for fixed B_0), and ensures Ω(g)=O(log B_0), because all other core primes exceed the tested shifts. Constants in the valuation bounds below may depend on B_0.

Use r_1=ceil(C_1t), r_i=ceil(C L_(i−1)) for i≥2, and consecutive distinct-divisor banks ending at

    x_1=P^(1/T²),     x_i=P^(s_i/r_i),      s_i=2^(i−d)/100 for 2≤i≤d.

These endpoints are ordered, since r_(i−1)/r_i≥10 for i≥3 with large H, and 2^d log T=o(T²). Their maximum product modulus through these degrees lies below P^.021 since Σ s_i<.02. The first mean is asymptotic to t, the second is ≤2log T, and for i≥3 the mean μ_i is at most log(2r_(i−1)/r_i)+O(1)≤2L_(i−1). The forced-test version of the same bound allows up to two deterministic successes. The endpoint preserves fixed positive modulus share s_d=.01; hence R_d=log(100 r_d) stays bounded independently of T.

For clarity the arithmetic comparison is via harmonic Bombieri–Vinogradov for one reduced class per tested product. With U_i the actual combined count of the first i banks, W_i its independent Bernoulli comparator, and Z any product of future-bank binomial coefficients of allowed orders, the weighted atom comparison has form

    |E[1(U_i=a) Z]−Pr(W_i=a) E Z*|
      ≤ ε_i E Z*/sqrt(t)+δ_i,

uniformly in a. For i=1 use weighted characteristic Taylor through degree r_1−1; the endpoint remainder is ≤2^r_1 times the r_1th binomial moment, paid by BV. Choose C_1 large so ε_1,δ_1 are exponentially small in t. For adding bank i apply Fourier inversion in its count b at each exact previous sum a−b, using stage i−1 on every Taylor coefficient with appended weight binom(bank i,k). The earlier relative error inflates by ≤exp(2μ_i), and the Taylor endpoint costs (2eμ_i/r_i)^r_i. Sum b<r_i at cost r_i. For b≥r_i weight the exact event by binom(bank i,r_i)/binom(b,r_i) and use Σ_(b≥r_i)1/binom(b,r_i)=r_i/(r_i−1). The resulting recursive error is

    ε_i ≲ r_i[ ε_(i−1) exp(2μ_i)+(1+ε_(i−1))(2eμ_i/r_i)^r_i ],
    δ_i ≲ r_i 3^r_i δ_(i−1).

All implied constants are uniform. Choose C large so 2e(μ_i+2)/r_i≤e^-8. The factor-ten preceding degree decrease and the common maximal model atom O(1/sqrt(t)) then give ε_i≤e^-r_i. The additive error stays exponentially small in t as Σ_(i≥2)r_i=O(log T). Before coefficients the BV saving can be made any fixed inverse power of log P, paying any exp(O(t)) first-degree inflation. The same argument weighted by one/two further forced prime tests or power tests uses moduli below P^.102, at most two forced bank successes, and at most O(log P) forced-power decomposition multiplicity per modulus (the powers of exponent ≥2 identify the forced primes, and same-prime pairs have O(log P) multiplicity); this too is paid by BV. Positive model weights are summed before the recursive comparison, so no per-modulus BV estimate is needed.

It follows that the actual U=U_d has atom bound O(1/sqrt(t)) everywhere, and central lower bound ≫1/sqrt(t) on |a−E W_d|≤sqrt(t), because W_d has the usual Gaussian lattice LLT (variance ∼t) and the uniform relative error ε_d≤e^-r_d is arbitrarily small fixed. This is a two-sided comparability, not an asymptotically vanishing relative atom discrepancy.

The actual full residual has the all-atom bound

    E[1(U=a)(V_j−U−R_d)^2] ≪_(B_0,H) 1/sqrt(t).

Indeed upper distinct primes in (x_d,P^.01] have bounded first/two comparator moments since x_d≥P^c for some fixed c>0. Apply the forced count version at each exact U atom. Repeated-exponent increments have bounded weighted second moments by the forced power-pair sum: distinct prime powers pay Σ_(q,e≥2)1/φ(q^e)<∞, and same prime pay Σ_(q,e≥2)(2e−3)/φ(q^e)<∞. For each comparator with ≤2 forced successes the maximal U atom remains O(1/sqrt(t)); cutoff tails of bigger tested powers cost negligible moments as in the [repeat and prime-power truncation argument](marked-tail.md) (BT for last power below P^.04, plus the large-repeat split). Primes above P^.01 contribute O(1) by size, and comparison with the stripped **distinct-prime** baseline pays the gcd: for stripped exponent e and gcd exponent s, |v₂(e+s+1)−1[e≥1]|≤s+(e−1)_+, by v₂(e+s+1)≤e+s and the cases e=0, e=1, and e≥2. Thus the extra contribution is bounded by Ω(g)=O(log B_0) plus the already paid repeats, not by a Lipschitz bound between divisor valuations.

Now sum min(Pr(U=a), E[1(U=a)(V_j−U−R_d)^2]/(v−a−R_d)^2) over a, using only the first bound when |v−a−R_d|≤1. The inverse-square sum converges uniformly in v. Therefore **sup_v Pr(V_j=v)≪_(B_0,H)1/sqrt(t)** on these actual retained shells.

A fixed-width actual strip likewise has a positive expected count. For |j−E W_d|≤sqrt(t)/4 take a large fixed W depending on the residual bound and let the bank deficit K+1+j−a−R_d lie in [2W,3W]. Each such central atom has probability ≫1/sqrt(t), and its conditional RMS is bounded, so at least half its probability falls in actual deficit [W,4W] by Markov for sufficiently large W. Summing over ≍W atoms per shift and ≍sqrt(t) shifts gives an expected count ≳W; the true atom upper gives ≪W. In particular the expected summed true angular energy is bounded below by a positive constant depending on W, since the least nontrivial distance for dyadic order ≤2^(4W) is at least 4·2^-4W, and W can exceed v₂(h) for any fixed harmonic h. No probability lower follows here from this expectation alone, no exact deficit-one lower is proved, and no cancellation bound for the full product follows from summed local energy. No whole V LLT is claimed. Private only.

[Back to the theorem](../0002-erdos-borwein-positive-word-density.md).
