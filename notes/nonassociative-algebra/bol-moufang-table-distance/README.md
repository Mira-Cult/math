# Table distance for left Bol and Moufang loops

*Mira Cult*

For two loop operations on the same set of $n$ labels, count the ordered pairs at which their products differ. Is there a constant $c>0$, independent of $n$, such that distance below $cn^2$ implies isomorphism?

- **0332.S1 (left Bol): no.** For every integer $d\ge3$, two nonisomorphic left Bol loops of order $2^{d+1}$ differ in exactly $2^{d+1}$ entries. Both can be nonassociative Bruck loops of exponent two.
- **0332.S2 (Moufang): yes.** Fewer than $n^2/20$ differences force isomorphism. The two identity labels need not coincide.

This answers the existence-of-a-constant question. It does not determine the optimal universal Moufang constant or establish the stronger [quarter-distance assertion of Drápal and Vojtěchovský](https://arxiv.org/abs/math/0701710).

## S1: a sparse row perturbation

Let V be the d-dimensional F₂ vector space, let λ be a nonzero linear form on V, and for nonempty S⊂ker λ not containing 0 put f=1_S. Define an operation on F₂×V by
```math
(a,x)*_S(b,y)=(a+b+f(x)\lambda(y),x+y).
```
The identity is (0,0), and either division is unique: solve the second coordinate first, then the first. Every square is the identity since f(x)λ(x)=0. Check the left Bol identity X*(Y*(X*Z))=(X*(Y*X))*Z: both base coordinates equal y+z and the first-coordinate discrepancy is
```math
 f(x)\bigl[\lambda(z)+\lambda(y+x+z)+\lambda(y+x)\bigr]
 +f(y)\bigl[\lambda(x+z)+\lambda(x)+\lambda(z)\bigr]=0.
```
The inverse map is the identity, hence an automorphism. These are Bruck loops in the left Bol convention.

Choose distinct nonzero p,q in ker λ and let S={p}, T={p,q}. Writing m=|V| and n=2m, the changed products have left base q and right base y with λ(y)=1; both central coordinates are free. Thus exactly 4(m/2)=n ordered entries change. The elements commuting with every element are precisely the two central choices over each x∈ker λ∖S: if x∈S test any λ(y)=1; if λ(x)=1 test a y∈S. Hence the two commutants have sizes m−2 and m−4, so no isomorphism is possible. Associativity would require f(x+y)=f(x)+f(y), obtained by testing the associativity defect on any z with λ(z)=1. Both supports have size at most 2, below the size m/2 of a nonzero linear form's support. Both loops are nonassociative and noncommutative; a Moufang loop of exponent two is commutative because each pair generates a group. The relative distance is 1/n, so no positive uniform c exists.

## S2: recover a common matching of left and right translations

Let L_x,R_x be the left and right translations of the product xy, and L'_x,R'_x those of x*y. Write d for normalized Hamming distance on permutations. This metric is bi-invariant and preserved by inversion; multiplication of permutation sequences costs at most the sum of the distances of corresponding factors. Two distinct left translations in either loop have distance exactly 1, by right cancellation, and the same is true for right translations.

Put ε equal to the normalized table distance, l_x=d(L_x,L'_x) and r_x=d(R_x,R'_x); each of l and r averages to ε. The Moufang identity (xy)(zx)=(x(yz))x and flexibility yield, with rightmost factor first,
```math
 L_{xy}=R_x L_x L_y R_x^{-1},
 \qquad R_{xy}=L_y R_y R_x L_y^{-1}.
```
For the first identity, compose on the right by R_x and evaluate at z. For the second, compose on the right by L_y and evaluate at z: (yz)(xy)=(y(zx))y=y((zx)y). The primed operations satisfy the same identities. Thus for xy=u,
```math
 d(L_u,L'_{x*y})\le 2r_x+l_x+l_y,\qquad
 d(R_u,R'_{x*y})\le 2l_y+r_y+r_x.
```
For fixed u let x vary over the loop and choose the unique y with xy=u. Then y also varies bijectively, so each bound averages to 4ε. There is a unique label within 4ε for each type of translation, since 8ε<1. The two labels coincide: use a decomposition whose sum of bounds is at most 8ε. Its primed product label is within 12ε of the selected label on each side, in the corresponding primed translation metric, so all labels agree. Call the common label φ(u). Distinct source left translations have distance 1, so the 4ε bound makes φ injective, hence bijective.

For any x,y, now apply the first identity to the source indices x,y and the primed indices φ(x),φ(y). The four factors cost at most 16ε, so d(L_{xy},L'_{φ(x)*φ(y)})≤16ε. On the other hand d(L_{xy},L'_{φ(xy)})≤4ε. Since 20ε<1, separation of primed left translations forces φ(xy)=φ(x)*φ(y). This proves the claimed isomorphism.

Run `python3 verify-loop-distance.py` for literal finite examples and a differing-identity Moufang comparison. These checks illustrate the proofs rather than replace them.


## Acknowledgments

AI assistance contributed to developing the proofs and checking the examples.
