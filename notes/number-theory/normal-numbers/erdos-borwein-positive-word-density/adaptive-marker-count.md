# Positive ordinary probability of an exact adaptive half marker

Fix 7/12<a<1 and sufficiently small θ>0 with θ<a/2, θ<1/2, and (a−θ)/(1−θ)>7/12. For H=⌊N^a⌋ (or any H between that and N), a positive ordinary proportion of n∈[N,N+H] have some positive j≤C loglog N with

    v₂(d(n+j))=j,

so the actual single coefficient d(n+j)/2^(j+1) in 2^(n−1)E equals a half modulo one. The constants are fixed; this is not an assertion about the whole phase.

Restrict to squarefree b≤N^θ and let j(b)=ω(b)+1. On genuine rows n=b p−j(b), p prime, p>sqrt(n+j(b))>b and d(n+j(b))=2^{ω(b)+1}; the corresponding term is exactly a half, before any other coefficient or carry. Keep j(b)≤C T, T=loglog N. For a fixed b the p interval has endpoints near N/b and length H/b, sufficiently long for the uniform effective Θ=7/12 short prime theorem (e.g. [Thorner–Zaman](https://arxiv.org/pdf/2108.10878), fixed modulus 3, sum the two reduced classes). The absence of a positive real zero of χ3 follows by pairing its alternating residue terms. The count is (1+o(1))H/[b log(N/b)] uniformly. The number of (n,j) incidences equals the sum of these counts since p is the unique prime >sqrt(n+j). The elementary squarefree harmonic estimate Σ_{b≤x} μ²(b)/b=log x/ζ(2)+O(1) (expand μ²) and partial summation give

    E F = (1/ζ(2)) log(1/(1−θ)) + o(1),

where F=F(n) is the number of certified marker offsets at ambient uniform n. Erasing j>C T loses o(1): for fixed z>1, Σ_{b≤N^θ} μ²(b) z^ω(b)/b ≤ ∏_{p≤N^θ}(1+z/p)=O_z((log N)^z), so choose C large and use z^(-CT)/(log N). Floors cost negligible relative errors; use H+O(1) for ambient normalization.

**Collision upper bound.** Two distinct marker offsets arise from b,c, with g=gcd(b,c), b=gb', c=gc' and gcd(b',c')=1. Their simultaneous equations imply b p−c q=D, where D=j(b)−j(c)=ω(b')−ω(c')≠0 by squarefreeness, and g|D. Hence g≤C T. If solvable, parameterize p=p0+c'v and q=q0+b'v on an interval length H g/(bc)+O(1); endpoint choice only determines p0,q0 and shifts v. Both primes are ≫N^(1−θ), and length is ≥N^(a−2θ) in order. Apply the standard dimension-two Selberg upper-bound sieve on this interval (sift only primes ≤N^η for a sufficiently small fixed η<a−2θ). Each prime ℓ has one or two forbidden parameter classes. If it divides a coefficient and the associated form is identically zero, or if two classes fill all residues at ℓ=2, no pair with both p,q≫N^(1−θ) exists. Otherwise a one-class local factor in place of two occurs only at ℓ|b'c'D/g: away from coefficient primes, roots coincide exactly when ℓ|D/g. The usual uniform sieve upper (interval residue errors O(1) per class, dimension ≤2) consequently bounds the count by

    O_a,θ( H g/(bc (log N)^2) · ∏_{ℓ|b'c'(D/g)}(1+C0/ℓ) ).

Explicitly the factor for converting two roots to one is (ℓ−1)/(ℓ−2)≤1+C0/ℓ for ℓ≥3, and ℓ=2 is absorbed by the fixed constant. This bound uses no lower prime-pair theorem.

Let w_ℓ=1+C0/ℓ. Absorb the factors from b' and c' into their respective squarefree harmonic weights ∏_{ℓ|b'} w_ℓ/ℓ and similarly for c'. For fixed g, enlarge the sum over each cofactor to all squarefree products supported by primes ℓ≤N^θ, ℓ∤g, with no size or cross-coprimality condition (positive majorant). Each normalization is ∏(1+w_ℓ/ℓ)=O(log N) by Mertens. On the normalized model the two counts Ω1 and Ω2 are independent sums of identical Bernoulli trials with q_ℓ=w_ℓ/(ℓ+w_ℓ). Their variance is ≍T uniformly in g≤C T: omission of g removes at most O(log T) reciprocal weight by the crude factor count, and O(1/ℓ²) errors sum. Thus D*=Ω1−Ω2 has CF modulus at most exp[−c T sin²(u/2)]. On any positive integer modulus q, inversion on the finite group gives

    Pr(q|D*) ≪ 1/q + T^-1/2,

by bounding the discrete Gaussian near its two endpoints. Keep q|D* even though it allows 0; the original nonzero D condition has already restricted divisor ranges below.

In the remaining D/g singular product expand ∏_{ℓ|D/g}w_ℓ=Σ_{d|D/g} μ²(d) C0^ω(d)/d. The original D is nonzero and |D|≤C T, so gd≤C T. Reordering summation and bounding the normalized probability by the preceding mod-(gd) estimate gives an ambient second factorial moment at most

    C Σ_{g≤CT} g^-1 Σ_{d≤CT/g} [μ²(d) C0^ω(d)/d] (1/(gd)+T^-1/2) = O(1).

The main product converges by the squared denominators; the error is O((log(T+2))^(C0+1)/sqrt(T)) by the positive Euler product and Mertens. This proves E F²≪1; Cauchy–Schwarz, or Paley–Zygmund, therefore gives Pr(F≥1)≫1 on the ordinary physical interval, not just on a prime-conditioned population. The same proof is uniform for all H in the stated range.

**Boundary.** These rows genuinely contain a factor −1 at some adaptive j, and their positive fraction is established. They can still contain two or more sign-changing factors, or compensating higher-deficit phases. The argument does not prove P(F odd)>0 uniformly (for the full set of valence-one-adjusted hits, not just the certified subset), a nonconstant signed product, any positive word density, or normality. Those are genuinely joint carry/phase statements.

**Single certified marker on positive mass.** A refinement keeps θ in the above Euler normalizers: ∏_(ℓ≤N^θ)(1+w_ℓ/ℓ)≪θ log N with an absolute constant, for fixed θ and large N. Choose η in the sieve once for 0<θ≤θ0<a/4. Its constants are then uniform in θ in that range, and the Fourier variance remains ≍T for each such fixed θ when N is large. Consequently E F(F−1)≪_a θ², whereas E F∼θ/ζ(2) as θ→0 (first N→∞ at fixed θ). Take θ small enough. Since F−F(F−1)≤1[F=1] pointwise, Pr(F=1)≫_a θ. In particular the selected product (-1)^F is separated from +1 on a positive ordinary fraction of every short physical window. This does **not** say that F counts all exact half factors, or that the complement's signs are independent: the actual full divisor phase remains unpaid.

[Back to the theorem](../0002-erdos-borwein-positive-word-density.md).
