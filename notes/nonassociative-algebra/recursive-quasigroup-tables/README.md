# Recursive quasigroup tables at orders 14 and 18

*Mira Cult*

A quasigroup is an operation whose table is Latin: every row and column is a permutation of the alphabet. We give explicit quasigroups of orders 14 and 18 for which the derivative $D(x,y)=f(y,f(x,y))$ is also Latin. These answer the two recursive-table questions (0340.S1 and S2). They are direct constructions, not first existence proofs. The [historical division core](0340-division-core.md) is a different operation.

## Construction

On the alphabet `Z_m ∪ {∞}`, set `f(∞,∞)=∞`, `f(∞,y)=y+a` and `f(x,∞)=x+b` for finite symbols. For finite x and y, write d=y−x modulo m and set `f(x,y)=∞` if d=h and `f(x,y)=x+W[d]` otherwise. All finite arithmetic is modulo m. The entries of W are indexed from zero.

| order | m | h | a | b | W |
|---|---:|---:|---:|---:|---|
| 14 | 13 | 9 | 4 | 0 | 2, 9, 3, 8, 7, 4, 12, 1, 5, 0, 6, 11, 10 |
| 18 | 17 | 15 | 16 | 14 | 7, 15, 4, 13, 16, 9, 2, 10, 6, 0, 11, 3, 12, 1, 8, 14, 5 |

Each W and the list `W[d]−d (mod m)` are permutations of the finite alphabet. At d=h the two offsets would be b and a, respectively. So in a finite row, all finite columns supply one infinity and every finite offset except b; the infinity column supplies b. In a finite column, the relative finite offsets are all except a and the infinity row supplies a. The infinity row and column are translations with infinity on their intersection. Thus f is Latin.

Set `D(x,y)=f(y,f(x,y))`. At fixed y, D is a composition of permutations (column y and row y of f). Simultaneous translation of all finite symbols, fixing infinity, preserves both f and D, so it suffices to check rows 0 and infinity. In both cases a≠h, so on finite y the infinity row of D is `f(y,y+a)=y+W[a]`; it ends with infinity. The offsets W[a] are 7 and 5, respectively. The rows at zero, with the integer m encoding infinity, are:
- m=13: 3, 6, 11, 7, 12, 2, 5, 8, 1, 9, 13, 0, 10, 4.
- m=17: 10, 9, 6, 14, 16, 4, 7, 3, 17, 15, 8, 11, 2, 5, 0, 12, 1, 13.

Each is a permutation; hence D is Latin.

## The corresponding recursive code

For every input pair take the codeword `(x,y,f(x,y),D(x,y))`. For input/output pairs involving $D$, recover the other input using its Latin row or column. For pairs involving $f$, use the corresponding Latin row or column of $f$. The input pair recovers the word by construction. Conversely from outputs z,w recover y via `f(y,z)=w`, then x via `f(x,y)=z`. Thus every two-coordinate projection is bijective. The minimum distance is three (at least three by injectivity, at most three since different words with one fixed input agree there). This is a full two-recursive MDS code.

## Prior existence from cyclic conjugation

Let Q be a quasigroup, and define the cyclic conjugate P by $P(a,b)=c$ iff $Q(b,c)=a$. Orthogonality of Q and P says that $(a,b)\mapsto(Q(a,b),P(a,b))$ is bijective. In the fiber with $P(a,b)=c$, the variable b is free and $a=Q(b,c)$, so orthogonality requires $b\mapsto Q(Q(b,c),b)$ to be a permutation for each c. For the opposite multiplication $f(x,y)=Q(y,x)$, this is precisely the row c of $D(x,y)=f(y,f(x,y))$; each column of D is always a composition of two permutations. For the inverse cyclic conjugate $P(a,b)=c$ iff $Q(c,a)=b$, the same argument directly gives D for f=Q. Thus either convention for naming the cycle yields the same existence implication.

[Bennett, Du and Zhang, J. Combin. Designs 9 (2001), pp. 297–308](https://onlinelibrary.wiley.com/doi/abs/10.1002/jcd.1013) prove existence of (3,1,2)-conjugate orthogonal diagonal Latin squares at all orders except 2, 3, 6 and possibly 10. In particular their theorem already implies the requested existence at 14 and 18; both were still listed as remaining cases in [Klimov's 2026 account](https://arxiv.org/html/2604.01105v2). The tables above give compact direct constructions.

## Reproduce the tables

Run `python3 verify-recursive-tables.py --tables` to print every entry of both multiplication and derivative tables and check all six two-coordinate projections. The [literal output](literal-recursive-tables.txt) is included. The proof above only needs the two displayed residue lists and the zero rows.

## Acknowledgments

AI assistance contributed to developing the proofs and checking the examples.
