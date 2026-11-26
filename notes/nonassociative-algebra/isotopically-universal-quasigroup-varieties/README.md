# Minimality of loops and an isotopically universal variety without loop parastrophes

**Mira Cult**

The variety of loops meets every quasigroup isotopy class and is minimal among varieties that do so. However, an isotopically universal quasigroup variety need not contain the whole variety of loops in any of the six orientations of the multiplication relation. These assertions concern all quasigroups, finite and infinite.

## Conventions and statements

A quasigroup has multiplication and the two divisions: $`x\backslash y`$ is the unique $`z`$ with $`xz=y`$, and $`y/x`$ the unique $`z`$ with $`zx=y`$. A loop is a quasigroup with a two-sided unit. The class of loops is a variety even in the division signature without a unit symbol: the identity $`x\backslash x=y/y`$ expresses exactly the existence of a common two-sided unit. A named unit in the loop signature can be eliminated from equations by replacing it with $`z\backslash z`$, using a fresh variable.

An isotopy from a quasigroup $`(Q,\cdot)`$ to $`(P,*)`$ is a triple of bijections satisfying $`\alpha(x)*\beta(y)=\gamma(x\cdot y)`$. A variety is *isotopically universal* if every quasigroup is isotopic to one of its members. A parastrophe is an orientation obtained by permuting the roles of $`x,y,z`$ in $`xy=z`$.

**Theorem 1.** The loop variety is isotopically universal, and none of its proper subvarieties is isotopically universal. More strongly, one countably infinite quasigroup has the property that every loop isotope of it has exactly the identities common to all loops.

**Theorem 2.** There is an isotopically universal quasigroup variety that does not contain the full loop variety or any of its parastrophes. The same construction is universal for all finite isotopy classes if restricted to its finite members.

## 1. One isotopy class tests every loop identity

For a quasigroup $`Q`$, write $`L_a(y)=a\cdot y`$ and $`R_b(x)=x\cdot b`$. For any $`a,b\in Q`$, the principal isotope
```math
x\circ y=R_b^{-1}(x)\cdot L_a^{-1}(y)
```
is a loop with unit $`c=a\cdot b`$. In fact $`R_b^{-1}(c)=a`$ and $`L_a^{-1}(c)=b`$, which give both unit laws. This already proves that loops are isotopically universal.

For each identity that fails in some loop, fix one witness assignment. Record the finite set of elements occurring in its two evaluations, together with the unit and all multiplication cells needed to reproduce the evaluations. For a division step $`x\backslash y=z`$, record $`xz=y`$; for $`y/x=z`$, record $`zx=y`$. Also record the unit row and column on the finite set. The result is a finite fragment of a genuine loop table, with the two final values distinct. There are only countably many identities, so countably many fragments suffice.

We will plant each such fragment in every principal isotope of a single countable quasigroup. Suppose a finite partial Latin table already has $`a\cdot b=c`$, and a fragment has unit $`e`$. Assign three labels $`U_i,V_i,X_i`$ to each element $`i`$ of the fragment, using $`U_e=a,V_e=b,X_e=c`$. All other labels are fresh, distinct from one another and from every previously used label. For each retained cell $`ij=k`$, insert
```math
U_i\cdot V_j=X_k.
```
Only the anchor $`(a,b)`$ is already an occupied cell. Any other new entry in row $`a`$ or column $`b`$ has fresh output: it represents a unit multiplication and its output is $`X_i`$ for some $`i\ne e`$. The rows and columns inside the fragment have no repeated outputs because the fragment came from a loop. Therefore no new row or column conflict is introduced.

The recorded unit cells give $`R_b(U_i)=X_i`$ and $`L_a(V_i)=X_i`$, so the principal isotope will satisfy $`X_i\circ X_j=X_k`$ on every retained cell. Since divisions are uniquely determined, the division steps also survive in any completion. Thus the same identity fails in the completed isotope.

To construct the ambient quasigroup, start with an empty table on a fixed countably infinite set. Enumerate three kinds of requirements: fill each specified cell; realize each specified output in each specified row and column; and plant each specified fragment at each ordered anchor $`(a,b)`$. At any finite stage only finitely many names are used. To fill a cell choose a fresh output; to place an output in a row or column where it does not yet occur, use a fresh column or row, respectively. Before planting a fragment, first fill its anchor if necessary. The increasing union is a Latin table in which every row and column contains every value, so it is a quasigroup. Every principal isotope realizes all the chosen failures.

Finally let $`P`$ be any loop isotope of this quasigroup. Choose $`a=\alpha^{-1}(e_P)`$ and $`b=\beta^{-1}(e_P)`$. Substituting these elements in the isotopy gives $`\alpha=\gamma R_b`$ and $`\beta=\gamma L_a`$. Hence $`\gamma`$ is an isomorphism from the principal isotope at $`(a,b)`$ to $`P`$. The set of loop identities valid in $`P`$ is therefore exactly the set valid in all loops. A proper subvariety imposes some further identity and cannot meet this isotopy class. This proves Theorem 1. The argument uses a countably infinite witness and does not establish the finite-only version of minimality.

## 2. A different universal variety

Let $`\mathcal W`$ be the quasigroup variety defined by constant square $`xx=yy`$ and by requiring the left and right translations by the common square to be involutions. More explicitly, with $`c=zz`$ these last two identities are $`c(cx)=x`$ and $`(xc)c=x`$. Here $`c`$ is a term, not an extra named constant.

Start with any quasigroup $`(Q,\cdot)`$ and choose $`d\in Q`$. The operation $`x\circ y=x\cdot(y\backslash d)`$ is an isotope, because the map $`y\mapsto y\backslash d`$ is bijective: for each $`v`$ there is a unique $`y`$ with $`y\cdot v=d`$. Its common square is $`d`$. Choose a label $`e`$, and in this isotope put $`A=L_e`$, $`B=R_e`$. Then $`D=A^{-1}B`$ fixes $`e`$.

Factor $`D=IJ`$ into involutions fixing $`e`$. On every nonsingleton orbit, index the elements so that $`D`$ is the shift $`j\mapsto j+1`$, using cyclic indices on finite orbits and integer indices on infinite ones. Put $`I(j)=-j`$ and $`J(j)=-j-1`$; on each singleton take both maps to be the identity. Relabel only the outputs of the isotope by $`\pi=IA^{-1}`$. Its common square becomes $`\pi(d)=e`$, and the two translations by $`e`$ become $`\pi A=I`$ and $`\pi B=ID=J`$. This table belongs to $`\mathcal W`$ and is still an isotope of the original quasigroup.

The cyclic group of order three has nonconstant squares, both in the original and opposite orientations. For the other four orientations consider the following loop, with unit $`0`$ and rows and columns indexed in the order displayed:
```text
0 1 2 3 4
1 0 3 4 2
2 3 4 0 1
3 4 1 2 0
4 2 0 1 3
```
In the left-division orientation the square is $`0`$, and one translation by $`0`$ is the right inverse map of the original loop. Its cycle $`(2\ 3\ 4)`$ makes it noninvolutive. In the right-division orientation the corresponding map is the left inverse map, the inverse of the same permutation. Opposites simply exchange the left and right translations. Thus all four division orientations of this table also fail the defining identities of $`\mathcal W`$. This proves Theorem 2.

## Context and reproducibility

The all-orders questions are attributed to Tomáš Kepka and Petr Němec at Loops ’03 in the [historical problem listing](https://en.wikipedia.org/wiki/List_of_problems_in_loop_theory_and_quasigroup_theory#Minimal_isotopically_universal_varieties_of_quasigroups). The [conference archive](https://web.archive.org/web/20070609134324/http://www.karlin.mff.cuni.cz/~loops03/) did not yield the complete original formulation for this account. The results above use the explicit signature and quantifiers stated here. Pigozzi’s [The Universality of the Variety of Quasigroups](https://doi.org/10.1017/S1446788700017791) concerns interpretation of varieties, a different notion of universality. No historical priority claim is made.

Run `python3 check.py` ([source](check.py)) to replay the order-three and order-five controls, the exclusions of all six parastrophes, and the relabeling procedure on those finite examples. These checks illustrate the constructions; they do not replace either all-orders proof. OpenAI models assisted with proof checking, replay, and exposition. No external refereeing or formal verification is claimed.
