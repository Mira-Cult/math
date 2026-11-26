# A counterexample to the cyclic projective-cube density conjecture

*Mira Cult*

A projective cube with $d$ generators is the set of sums over all nonempty subsets of the generator indices. The generators lie in $\mathbb Z/N\mathbb Z$; repetitions, zero and coincident sums are permitted. [Yuchen Meng's conjecture](https://arxiv.org/html/2311.12318v2) (Conjecture 2 of the preprint, Conjecture 4 of the journal article) asserts that when $d\mid N$, a set containing no such cube has size at most $(d-1)N/d$.

Let S⊂Z/16Z consist of all odd residues, all residues 2 mod 4, and the single residue 8. It has 8+4+1=13 elements. It contains no projective 5-cube, including cubes with repeated generators. Therefore its full preimage A under the group homomorphism Z/80Z→Z/16Z has 5·13=65 elements and is also 5-cube-free: a cube in A would map to a cube in S, because every nonempty index-subset sum maps to the corresponding sum of the projected multiset. In particular 5|80 and |A|=65>4·80/5=64, refuting the requested universal bound. More generally all N multiples of 80 give density 13/16 and the same obstruction at d=5. This argument does not presume projected generators are distinct or nonzero; zero is simply outside S.

## Analytic cube-freeness in Z/16Z

Suppose five actual indexed generators have every nonempty subset sum in S. Since singletons occur, all are in S. Call an even generator B-type when it is 2 mod 4 (residue 2,6,10,14), and E-type when it is 8. The only admissible 0 mod 4 residue is 8. All sums below are modulo 16.

There cannot be two E-type generators, whose sum is zero. A pair of B-types must sum to 8. Three B-types would then be equal by comparing pair sums, impossible because twice a B-type is 4 mod 8. Nor can two B-types coexist with an E-type: the sum of all three would be 8+8=0. Hence there are at most two even generators, and at least three odd ones.

Two odd generators with opposite residues mod 4 must sum to 8. Two disjoint opposite pairs are impossible, as their four-term sum would be 0. Thus if both odd signs occur, either a disjoint opposite-pair contradiction already applies or exactly one odd generator is in the minority mod 4 class. In the latter case every majority odd generator equals the same u, by subtracting its pair-sum equation with the unique minority v; in particular u+v=8. Note also that four equal odd terms never sum to 8, because 4u is 4 or 12 mod 16.

* **Five odd generators.** If mixed mod 4, there are four equal majority terms, impossible by the preceding observation. If all congruent mod 4, every four-term sum must be 8. Comparing the five four-term sums makes all five generators equal, again impossible.
* **Four odds and one even.** In the mixed case they are u,u,u,v with u+v=8. The even generator cannot be E-type because of the opposite pair. Write it as e of B-type. Then 2u+e must be 8 (it is 0 mod 4), and the sum of all five generators is (u+v)+(2u+e)=0. In the single odd-sign case, the four-odd sum must be 8, excluding E-type as the fifth generator. For B-type e every odd pair plus e must be 8. Hence all odd pair sums are equal, making all four odds equal; contradiction.
* **Three odds and two evens.** If the odds are mixed, an opposite pair gives 8, and separately either an E-type singleton or the two B-types together give 8, again producing a joint 0. If all odds have the same sign mod 4, there is at least one B-type generator e and every odd pair plus e must be 8. Thus the three odds are equal to u, and each B-type generator equals 8−2u. Two such B-type generators cannot be equal (their doubled value is 4 mod 8, not the required 8). The remaining possibility of one B-type and one E-type produces 2u+e+8=0.

These cases exhaust all five indexed generators. Every use of a pair/triple/quadruple uses distinct indices, even when those indices' values agree; all coincidences are therefore legal and handled.

## Further exact counterexamples

Excluding $0,6,30$ from $\mathbb Z/36\mathbb Z$ gives a set of size $33$ with no projective $10$-cube. Excluding $0,12,60$ from $\mathbb Z/72\mathbb Z$ gives a set of size $69$ with no projective $15$-cube. These two claims use the [exhaustive verifier](check-projective-cubes.cpp). Compile and run it with `g++ -std=c++17 -O3 check-projective-cubes.cpp -o check-cubes && ./check-cubes`.

The verifier stores the attainable subset sums of a prefix, including the empty sum zero, in a cyclic bitset. To extend by $x$, translate the bitset by $x$. The translated set contains exactly the new sums using the new index, so a prefix is rejected exactly when a new sum is forbidden. Only weakly increasing lists are tried, retaining every multiset once. A zero generator is forbidden by its singleton and may be omitted at the outset. Thus successful depth counts of zero prove cube-freeness; the full depth counts are asserted in the verifier. Every larger-dimensional cube would contain a cube from its first prescribed number of indices. Pullback to cyclic orders divisible by both the base order and the chosen dimension preserves the density and cube-freeness. This gives counterexamples at dimensions $10,11$ from the first base and at dimensions $15$ through $23$ from the second. For example, $N=72,d=18$ would give an upper bound of $68$ instead of $69$.

## Dimension four still obeys the conjectured bound

**Theorem.** If A⊆Z/NZ contains no projective 4-cube, with repeated and zero generators allowed, then |A|≤3N/4 for every positive N. When $4\mid N$, the nonzero classes modulo four give equality. Indeed, the five prefix sums of four generators modulo four, including the empty sum, include two equal values. Their difference is the sum over a nonempty consecutive set of generator indices and is zero modulo four. This includes composite N not covered by Meng's Theorem 5.

Write B for the complement. If |B|<N/4 and x,2x,3x∈A, the union of the four translates B−jx, 0≤j≤3, has size at most 4|B|<N. A y outside it makes all nonempty subset sums of (x,x,x,y) lie in A, a contradiction. Thus B hits every triple (x,2x,3x), including literal repetitions if they occur.

Let b=v₃(N). Partition cyclic residues into ordinary 3-adic layers L_j for 0≤j<b and terminal layer L_b=3^b Z/NZ. Their sizes are 2N/3^{j+1} for j<b, and N/3^b at the terminal. (If b=0 only the terminal is present.) Give each source x in nonterminal even layer weight 1/3, each source x in nonterminal odd layer zero, and every terminal source weight 1/4 if b is even or 1/12 if b is odd.

Count target load with multiplicity: each x supplies its weight separately to x,2x,3x. Every target load is at most one. For a nonterminal even layer, the source's first two maps have at most 1 and 2 same-layer preimages, while possible prior 3-preimages come from an odd layer of weight zero. For a nonterminal odd layer, only the preceding even layer contributes, with at most three 3-preimages. In L_b the maps 1 and 3 have one preimage each (3 is invertible on L_b) and 2 has at most two, so the within-terminal load is at most four times its source weight. The preceding layer exists only for b>0, and when b odd is positively weighted. Every terminal target then has precisely two 3-preimages from L_{b−1}: on the 3-primary cyclic coordinate it has three preimages, one zero (terminal) and two of exact valuation b−1, while on the coprime coordinate the preimage is unique. Thus the terminal load is at most 4/4=1 if b even and 2/3+4/12=1 if b odd.

The total even nonterminal layer mass is 3N/4·(1−3^{-b}) for b even and 3N/4·(1−3^{-(b+1)}) for b odd, by a geometric series. Its source weight after multiplication by 1/3 is N/4 times the respective parenthesis. The terminal contributes N·3^{-b}/4 or N·3^{-b}/12, respectively, topping up to N/4 in either case. Since B hits each weighted source triple, total source weight ≤ total target load in B ≤ |B|, contradiction. No properness assumptions or exclusions of repeated points.


## A positive family with a single small prime

In the cyclic group Z/NZ let B be the complement of a projective-d-cube-free set A (generators may repeat and may equal zero). If |B|<N/d then B must meet {x,2x,…,(d−1)x} for every x. Otherwise take d−1 copies of x and an additional y. At most d|B| choices of y are blocked by the d forbidden translates y+jx∈B, j=0,…,d−1; one more y is possible, giving all real nonempty subset sums in A. Coincident sums only make the avoidance easier.

Suppose there is a prime p<d≤2p dividing N and every other prime divisor of N is at least d. Then among 1,…,d−1 exactly one multiplier p is not a unit. Write b=v_p(N); let L_j be the residues of exact valuation j<b and L_b the terminal multiples of p^b. Thus |L_j|=(p−1)N/p^(j+1) for j<b and |L_b|=N/p^b. Each unit multiplier gives one preimage within each valuation class. Multiplication by p advances j one step, with at most p preimages. A terminal site has precisely p−1 preimages in L_(b−1) and one preimage in L_b, by the Chinese remainder decomposition between the p-power and the coprime factor.

Write a=d−2 and w=1/max(a,p). Assign weight w to a source x in any even nonterminal class, weight zero in odd nonterminal classes, and terminal weight 1/(d−1) for b even or (1−(p−1)w)/(d−1) for b odd. Every site receives total weighted incidence at most one: nonterminal even classes receive a w from units and no incoming p-load, odd classes receive at most p w from the preceding class, and terminal load uses at most the stated one own p-preimage plus a own unit preimages and p−1 previous ones if previous is active. Multiple occurrences in a single diagonal count as separate incidences, so a hitting set can only cost more.

Let T=pw/(p+1). The total assigned weight divided by N, summing the even layers, is
```
T(1−p^(−b)) + p^(−b)/(d−1)                              (b even)
T(1−p^(−b−1)) + p^(−b)(1−(p−1)w)/(d−1)                 (b odd).
```
In each parity the expression is between the limiting value T and its respective value at b=0 or b=1, since it is affine in p^(−b). The first endpoint is 1/(d−1). The second is [1+(p−1)w(d−2)]/[p(d−1)]. If d≥p+2, w=1/(d−2), so the second endpoint is also 1/(d−1), and T≥1/d since d≤2p≤2p+2. If d=p+1, w=1/p, then T=1/d and the second endpoint exceeds 1/d by 1/[p³(p+1)]. Thus the total assignment is at least N/d. Every hitting set has size at least this total. The strict contradictory hypothesis above is therefore impossible.

In the indexed setting d|N, this supplies in particular every prime d with a single smaller prime factor p of N satisfying p<d<2p. Examples include d=5 and odd N divisible by 15 (other factors ≥5), or d=7 and N with smaller prime factors only 5. It does not claim the unrestricted conjecture.

For d=5 and odd N there is a slightly stronger statement about diagonals: if 3∤N all four multipliers are units and uniform weights 1/4 apply; otherwise the d=4 layer balance applies with 1,2,4 as the three own-layer bijections, p=3 as the advancing multiplier, nonterminal even weight 1/3, and terminal 1/4 or 1/12. Total weight is exactly N/4. In either case the true d=5 bound follows by five translates and applies even when 5∤N.


The dimension-five base case can also be checked with `python3 check-projective-five.py` ([source](check-projective-five.py)). This check is not part of its analytic proof. The cyclic counterexamples do not address the distinct interval conjecture of Eberhard and Pohoata.

*Acknowledgment.* AI-assisted mathematical research and preparation.
