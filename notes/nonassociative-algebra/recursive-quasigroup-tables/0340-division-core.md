# Latin division cores at orders 14, 18, 26 and 42

*Mira Cult*

The historical question (0340.S3) asks for quasigroups with Latin division core $C(x,y)=f(x,y\backslash x)$ at four specified orders, where $y\backslash x$ is the unique solution of $f(y,z)=x$. This is not the [first recursive derivative](README.md). We give compact witnesses; the 1987 conjugate-square theorem already implies their existence.

## Equivalence with squared right translations

Given a quasigroup f, write $C(x,y)=f(x,L_y^{-1}(x))$ and $B(y,u)=f(f(y,u),u)$. Fix x. Then $y\mapsto L_y^{-1}(x)$ is a permutation by the Latin columns, so every row of C is a permutation. For fixed y substitute $x=f(y,u)$, a permutation of u. Then $C(f(y,u),y)=B(y,u)$. Thus C is Latin exactly when every row of B is a permutation. Each B column is already the square of a permutation. This tests the source's division formula directly; it is not the earlier derivative $f(u,f(y,u))$.

## Explicit one-point cyclic completion

Use the alphabet $\mathbb Z_m\cup\{\infty\}$. Put $f(x,x)=\infty$ for all symbols, $f(x,\infty)=x+1$ for finite x, $f(\infty,y)=y+1$ for finite y, and for distinct finite x,y put $f(x,y)=x+W[y-x]$, using residues mod m and starting the lists at index zero:
- m=13: W=(1,9,11,2,8,7,3,0,6,12,10,5,4).
- m=17: W=(1,0,9,6,10,15,3,16,12,5,4,11,14,8,2,13,7).
- m=25: W=(1,14,12,2,19,0,22,9,17,13,18,3,5,7,21,11,16,6,15,24,23,8,20,4,10).

Both W and W[d]−d are permutations of the residues. Their missing zero-index value is the offset 1 filled at infinity, so f is Latin, because each finite row loses one offset and the infinity column restores it, while each finite column likewise loses one offset and the infinity row restores it. Simultaneous translations of all finite symbols, fixing infinity, preserve B. For finite y, $B(\infty,y)=f(y+1,y)=y+1+W[-1]$ is a translation; at y=∞ it is ∞. The remaining orbit of rows is represented by row zero. With $m$ denoting infinity, those rows of $B$ are:

- $m=13$: 1, 3, 6, 11, 7, 12, 5, 0, 4, 9, 13, 8, 10, 2.
- $m=17$: 1, 0, 13, 8, 4, 14, 9, 11, 3, 15, 7, 17, 10, 6, 16, 5, 12, 2.
- $m=25$: 1, 19, 23, 16, 12, 0, 10, 13, 8, 21, 24, 20, 14, 4, 11, 5, 25, 9, 17, 22, 18, 15, 7, 3, 6, 2.

Each is a permutation, proving the three division-core witnesses. The checker constructs and checks every line of $f$, $C$ and $B$ directly.

## Product to obtain order 42

The componentwise product of two Latin operations is Latin, and left division, the core, and the squared right translations all commute with that product. Addition on the order-three cyclic group has core 2x−y, Latin since both 2 and −1 are units. The product of the order-14 witness above with addition mod 3 has order 42 and Latin core. The verifier checks all rows and columns of this product, not just each factor.

## Historical formulation and prior existence

[Mahesar and Sorge, Property Preserving Generation of Large Size Quasigroup-structures, §4, p. 25](https://arw.csc.liv.ac.uk/year/2010/ARW-2010-main.pdf#page=25) explicitly pose the four orders 14, 18, 26 and 42 using $C(x,y)=Q(x,y\backslash x)$, not a property of a loop isotope. Here $y\backslash x$ is the unique z with $Q(y,z)=x$. The same term is the loop-core convention in [Larionova-Cojocaru and Syrbu (2015), p. 57](https://msuir.usm.md/bitstreams/edb5157c-a66e-4b79-bb67-518962456604/download).

For fixed x, $y\mapsto y\backslash x$ and $z\mapsto Q(x,z)$ are permutations, so the rows of C are automatic. In column y put $x=Q(y,z)$ and vary z. Then
```math
 C(Q(y,z),y)=Q(Q(y,z),z)=R_z^2(y),\qquad R_z(u)=Q(u,z).
```
Thus the remaining condition is that $z\mapsto R_z^2(y)$ is a permutation for each y. On the other hand the (3,2,1)-conjugate of Q is $Q'(x,z)=R_z^{-1}(x)$. Setting $x=R_z(y)$ in the orthogonality map $(x,z)\mapsto(Q(x,z),Q'(x,z))$ yields $(R_z^2(y),y)$. This proves equivalence, not just one implication.

[Bennett, Wu and Zhu, Some new conjugate orthogonal Latin squares, J. Combin. Theory Ser. A 46 (1987), pp. 314–318](https://www.sciencedirect.com/science/article/pii/0097316587900094) give (3,2,1)-conjugate orthogonal squares at every positive order except 2 and 6. Their theorem and the equivalence answer all four historical orders positively. The independent constructions now verify these four orders directly as well. The 1987 result is separate from the 2001 cyclic-conjugate result.

## Replay

Run `python3 verify-division-core.py` to construct the multiplication, left division and core and test every line at all four orders.

## Acknowledgments

AI assistance contributed to developing the proofs and checking the examples.
