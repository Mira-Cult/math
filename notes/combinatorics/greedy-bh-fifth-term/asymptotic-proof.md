# A body-centered cubic covering for the leading term

The fifth positive greedy $B_h$ term satisfies $\gamma_5(h)=h^4/3+O(h^3)$. This proof uses no finite search. See the [main note](README.md) for conventions and the exact formula. For prior formulas, forbidden-difference setup, and a lower bound used to start below the asymptotic range, use Kevin O'Bryant, [Bounds for Greedy B_h-sets, arXiv:2312.10910v3](https://arxiv.org/html/2312.10910v3), §3, Theorem 1.2 and Appendix A.

## Exact growth and integer kernel

Write g=(1,g_2,g_3,g_4) for the first four positive terms. They satisfy
  g_2=h+1, g_3=h²+h+1,
  $g_4=h^2\lfloor(h+3)/2\rfloor+\lfloor3h/2\rfloor+1$.
Let P(d)=sum max(d_i,0), N(d)=sum max(−d_i,0) for a vector in any dimension. An integer x larger than g_4 is forbidden iff for some integer 1≤r≤h there is d∈Z^4 with
  d·g=r x,   P(d)≤h,   N(d)≤h−r.
Indeed cancel common terms in an equal h-sum and orient the side with r copies of x; remove any zero terms and use zero to pad. Equality not involving x is impossible since the old prefix is B_h.

Exactly write g_4=p g_3+q g_2+s with p=floor((h+3)/2), q=−floor((h+1)/2), s=floor(h/2), checked in each parity. A Z-basis for ker(g) is
  k_1=(−h−1,1,0,0), k_2=(−1,−h,1,0), k_3=(−s,−q,−p,1).
The relations are exact; successively subtract k_3,k_2,k_1 to cancel coordinates 4,3,2, and coordinate 1 is then zero by evaluation. Let B_h be the 3×3 matrix of the first three coordinates of these basis vectors divided by h. Its limit B has columns
  (−1,0,0), (0,−1,0), (−1/2,1/2,−1/2).
The lattice BZ³ is L=Z³+Z(1/2,1/2,1/2) (the third standard basis vector is an integral combination of these columns, as are the first two; their remaining coset is the indicated half-shift). B_h−B=O(1/h) and B is invertible. In particular a bounded displacement in B_hZ³ uses only bounded integer coefficients, uniformly for large h; the same holds for B.

## Elementary limiting covering and its sharp hole

Claim K+L=R³, where K={u∈R³:P(u)≤1/3,N(u)≤1}. For any vector there are two residue phases: its fractional coordinates and their simultaneous half-shift modulo 1. Sort one phase as a≤b≤c in [0,1). Any of these three conditions suffices:
  (i) a+b≤1/3;
  (ii) a≤1/3 and b+c≥1;
  (iii) a+b+c≥2.
For (i) retain the first two coordinates and subtract one from the last. For (ii) retain only the first and subtract from the other two. For (iii) subtract one from all three.

Choose the phase with at most one coordinate ≥1/2, since the half-shift interchanges the two sides of that threshold. If all coordinates are below 1/2, either (i) holds or the sum is greater than 1/2, since c≥(a+b)/2. In the latter case the shifted phase satisfies (iii). If only c≥1/2, the shifted sorted phase is (c−1/2,a+1/2,b+1/2). If c≤5/6 this satisfies (ii). If c>5/6 and b+c<1, then b<1/6 and original (i) holds. If c>5/6, b+c≥1, and a≤1/3, original (ii) holds. In the last case a>1/3, so shifted sum a+b+c+1/2>2. This proves covering on all real vectors.

Robust form: for 0<η<1, K+η(1,1,1) is contained in {u:P(u)≤1/3+3η,N(u)≤1−η} and its lattice translates still cover. Indeed the shift can increase P by at most 3η and either N was below η and becomes zero, or the shift removes at least η of N.

For the sharp gap (needed below), take y with each coordinate near 1/6, but smaller than it by a large multiple of an allowed error scale ε. In the unshifted phase, negative budget 1 forces at least two coordinates positive, since any two negative coordinates have total magnitude near 5/3. The positive cost is thus at least 1/3 minus that error allowance. In the shifted phase, each fractional coordinate is near 2/3, less than 2/3 by a controlled margin; any positive coordinate already costs near 2/3, while three negative coordinates cost strictly more than 1. The following proof controls these allowances in the finite lattice.

## Lower bound with O(h³) loss

Consider x in [h^4/8, h^4/3−C h³] and let h tend to infinity. Successively divide x by g_4, then its remainder by g_3, then by g_2, leaving the final units remainder. This gives an exact integer solution d^0·g=x with all first three coordinates nonnegative O(h), and d^0_4=2x/h³+O(1) uniformly for this range. Indeed g_4=(1/2)h³+O(h²), and all successive ratios of place values are O(h).

Write y=d^0_[1:3]/h. The robust body covering gives an n∈Z³ for which y+Bn has P≤1/3+3η and N≤1−η. Its first three coordinates stay in a bounded box for every 0<η<1/4, as does y. Thus n is uniformly bounded by invertibility of B, with no dependence on the eventual constant in η. The true integer solution d=d^0+Σ_i n_i k_i has first three scaled coordinates y+B_h n, which differ from y+Bn by O(1/h) in l1 norm. Both P,N are 1-Lipschitz for that norm. Choose η=D/h with fixed D sufficiently large to absorb the latter error and a further 1/h; then N(d_[1:3])≤h−1 and P(d_[1:3])≤h/3+O(1). Its fourth coordinate differs from d^0_4 by n_3=O(1), so remains positive for x≥h⁴/8 and is at most 2h/3−2C+O(1) on the whole range. Choose C large enough that P(d)≤h. Thus all these x larger than g_4 are forbidden already with r=1. O'Bryant's Theorem 1.2 ensures no admissible x below h⁴/8. This gives gamma_5(h)≥h^4/3−O(h³).

## Upper bound by an actual near-hole integer

Let d^0_i=floor(h/6)−A for i=1,2,3 and d^0_4=ceil(2h/3+C), with fixed large positive constants A,C chosen below, and set x=d^0·g. Then x=h^4/3+O(h³), and for sufficiently large h, 2x>h g_4. Thus r≥2 cannot forbid x, since d·g≤h g_4 for P(d)≤h.

For contradiction suppose some d forbids x with r=1. By the integer kernel, d=d^0+Σ_i n_i k_i for n∈Z³. Since P(d)≤h, N(d)≤h−1, the first three scaled coordinates are bounded in l1 by 2. For all large h, y=d^0_[1:3]/h is bounded by 1 in l1, uniformly independently of fixed A,C. Therefore B_h n=d_[1:3]/h−y has bounded l1 norm, and n is uniformly bounded independently of A,C. Choose absolute constants E,F so that the l1 difference between B_hn and Bn is ≤E/h and |n_3|≤F. Then d_4≥2h/3+C−F and hence
   P(d_[1:3]/h) ≤ 1/3−(C−F)/h,
   N(d_[1:3]/h) ≤ 1.
The exact limiting representative v=y+Bn is within E/h in l1 of d_[1:3]/h. Therefore P(v)≤1/3−(C−F−E)/h and N(v)≤1+E/h.

The fractional coordinates of v are either all y_i or all y_i+1/2, since Bn lies in L. In the first phase, at least two coordinates of v must be positive, since two negative values have magnitude sum approaching at least 5/3, too large for N(v)≤1+E/h. Each positive coordinate costs at least 1/6−(A+1)/h. Thus P(v)≥1/3−2(A+1)/h. In the shifted phase, any positive coordinate costs at least 2/3−(A+1)/h and is excluded for large h; if all are negative, N(v)≥1+3A/h, contradicting N(v)≤1+E/h when 3A>E. Choose this A first, and then C>F+E+2(A+1) to contradict the first phase as well. Thus x is an actual admissible integer. Being the greedy first admissible integer above g_4, gamma_5(h)≤x=h^4/3+O(h³). The conjectured expansion follows.
