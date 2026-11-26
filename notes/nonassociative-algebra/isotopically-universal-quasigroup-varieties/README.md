# An isotopically universal quasigroup variety without loop parastrophes

**Mira Cult**

An isotopically universal quasigroup variety need not contain the full loop variety in any of the six orientations of the multiplication relation. The construction works for all quasigroups, finite and infinite.

## Conventions and statement

A quasigroup has multiplication and the two divisions: $`x\backslash y`$ is the unique $`z`$ with $`xz=y`$, and $`y/x`$ the unique $`z`$ with $`zx=y`$. A loop is a quasigroup with a two-sided unit. The class of loops is a variety even in the division signature without a unit symbol: the identity $`x\backslash x=y/y`$ expresses exactly the existence of a common two-sided unit. A named unit in the loop signature can be eliminated from equations by replacing it with $`z\backslash z`$, using a fresh variable.

An isotopy from a quasigroup $`(Q,\cdot)`$ to $`(P,*)`$ is a triple of bijections satisfying $`\alpha(x)*\beta(y)=\gamma(x\cdot y)`$. A variety is *isotopically universal* if every quasigroup is isotopic to one of its members. A parastrophe is an orientation obtained by permuting the roles of $`x,y,z`$ in $`xy=z`$.

**Theorem.** There is an isotopically universal quasigroup variety that does not contain the full loop variety or any of its parastrophes. The same construction is universal for all finite isotopy classes if restricted to its finite members.

## Constructing the variety

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
In the left-division orientation the square is $`0`$, and one translation by $`0`$ is the right inverse map of the original loop. Its cycle $`(2\ 3\ 4)`$ makes it noninvolutive. In the right-division orientation the corresponding map is the left inverse map, the inverse of the same permutation. Opposites simply exchange the left and right translations. Thus all four division orientations of this table also fail the defining identities of $`\mathcal W`$. This also rules out containment of the full unipotent left-loop or right-loop variety: left division of a loop has constant square and a left identity, and right division has constant square and a right identity. The appropriate division parastrophes of the order-five loop above fail the identities of the universal variety.

## Context and reproducibility

[Kepka and Němec, *Unipotent Quasigroups* (1977), p. 15](https://dml.cz/bitstream/handle/10338.dmlcz/142401/ActaCarolinae_018-1977-2_3.pdf) already established minimality of the loop variety and asked whether a universal variety must contain all loops or a full unipotent one-sided loop variety. The result here is the negative answer to that containment question, not the known minimality theorem. Pigozzi’s [The Universality of the Variety of Quasigroups](https://doi.org/10.1017/S1446788700017791) concerns interpretation of varieties, a different notion of universality. No historical priority claim is made.

Run `python3 check.py` ([source](check.py)) to replay the order-three and order-five controls, the exclusions of all six parastrophes, and the relabeling procedure on those finite examples. These checks illustrate the constructions; they do not replace the all-orders proof. Mira’s dots, using OpenAI’s GPT Astra models, assisted with proof checking, replay, and exposition. No external refereeing or formal verification is claimed.
