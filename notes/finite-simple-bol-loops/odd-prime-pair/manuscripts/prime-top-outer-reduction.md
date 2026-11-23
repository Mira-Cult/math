# Canonical signed envelopes and the reciprocal Hall reduction

**Mira Cult**

This note reduces an arbitrary finite simple proper left Bol loop of order $`p^a q`$, with distinct odd primes, to its canonical odd signed envelope and the reciprocal Hall architecture. It supplies the outer hypotheses used by the [prime-top classification](0134-prime-top-two-types.md). The strict cut and normal generation proofs used below are also available in the [signed-folder foundations](../../packet/manuscripts/odd-folder-radicals.md#strict-defect-for-every-proper-invariant-normal-subgroup).


<a id="odd-prime-pair-canonical-coverage-and-85293-integration"></a>

## Canonical coverage for every simple proper odd-order left Bol loop
The oddness, solvability and sign hypotheses used in the group reductions are automatic for all finite simple proper left Bol loops of odd order.
### Canonical faithful action and oddness

Let Q be any finite simple proper left Bol loop of odd order, G=LMlt(Q), K its left translations, and H the stabilizer of its identity. G acts faithfully by its definition and transitively because K sends the identity to every loop element. Thus H is ordinary core-free and |Q|=[G:H]. K generates G and is a left transversal to every conjugate of H: its evaluations at a fixed point y are all distinct, by the right division law for the loop.

The primary source is Foguel–Kinyon–Phillips, [On Twisted Subgroups and Bol Loops of Odd Order, arXiv v2](https://arxiv.org/pdf/math/0208231v2), published in [Rocky Mountain J. Math. 36 (2006), 183–212](https://doi.org/10.1216/rmjm/1181069494). Numbering here is the linked v2. Example 5.1 identifies K as a twisted subgroup. Left power alternativity gives L_x^j=L_(x^j). If a power fixes any point y, right cancellation forces x^j=1, so all cycles have length the order of x. Thus each mark order divides |Q| (also their Prop. 6.1). Their Lemma 4.1, or the unique square root in the odd cyclic subgroup of any mark, makes K 2-divisible. Their Theorem 4.14 then gives odd |G|; Theorem 4.17, stated directly for loops as Theorem 6.7, gives that G uses only primes in |Q|. The index ensures all primes of |Q| are present. Feit–Thompson gives solvability of G, not solvability of Q.

### Canonical sign and actual full class

In the same source, Corollary 5.11 states that the loop's Aschbacher radical is an associative normal subloop. Simplicity and nonassociativity force it to be trivial, not the whole loop. Proposition 3.9 (citing Aschbacher's Theorem 2.2) then gives the unique automorphism t inverting every mark. It has order exactly two (rather than merely dividing two) because a nonidentity mark has odd order and is not its own inverse.

In G⋊⟨t⟩, each k t is an outside involution. The set Kt is stable under conjugation by x∈K: x^−1(k t)x=(x^−1 k x^−1)t, which belongs to Kt by twisted closure. Since K generates, Kt is G-conjugacy invariant. G has odd order, so all the outside involutions are in a single G-conjugacy class by coprime complement conjugacy. Kt contains t, so equals that whole class. This verifies the full inverted mark hypothesis and gives |K|=[G:C_G(t)], whence |H|=|C_G(t)|. No assumption that t acts by inversion as a permutation of Q is made.

### Strict signed cuts and normal generation needed by the reciprocal theorem

For any nontrivial proper t-stable normal I⊳G, every t-fixed coset of I contains a fixed representative (an involution on an odd set has a fixed point). Thus the fixed-point map onto C_(G/I)(t) is surjective with kernel C_I(t). Outside involution lifting through I gives that the K image is the full inverted set of G/I. It covers all left cosets of the projected stabilizer HI/I, including for every conjugate. The ratio of its size to that index is |C_I(t)|/|H∩I|. Hence equality would give actual quotient transversality and a loop homomorphism from Q to the quotient folder, by projecting the multiplication relation on representatives. If HI=G, equality would make all marks project to identity, so K⊂I, contradicting generation. If HI≠G, the quotient is nontrivial. The kernel cannot be trivial: under equality its order is |K∩I|=[I:H∩I], greater than one since otherwise normal I≤H contradicts core-freeness. Simplicity therefore rules out equality. This proves the required strict signed cuts.

For normal generation, the map from Q to G/HG′ is a surjective homomorphism to a group, by the same representative multiplication relation (HG′ is normal). If this group were nontrivial, simplicity would force injection, contradicting nonassociativity. Thus HG′=G. Since G is solvable its quotient by the normal closure of H cannot be nontrivial perfect, so H normally generates G. These are the simple/proper inputs to the reciprocal theorem, not additional conditions on Q.

<a id="odd-hall-top-prime-exponent-architecture"></a>

## Inverted abelian top rank costs prime factors in the loop order
Let $`D,H,t`$ be an odd signed
folder and put $`N=O_p(D)`$, for odd $`p`$.
Suppose $`D/N`$ has a sign-stable normal nilpotent Hall
$`p'`$-subgroup $`\bar B`$, and an abelian $`p`$-group top
$`P=(D/N)/\bar B`$ on which sign acts as inversion.
Write $`d(P)`$ for the least number of generators of $`P`$.
For each prime $`q`$ dividing $`|\bar B|`$, let $`B_q`$ be
its actual normal Sylow subgroup **in $`D/N`$** and let
$`r_q^-=\dim(B_q/\Phi(B_q))^-`$ for the induced sign.
Then

```math
d(P)\ \le\ \sum_{q} r_q^-\
       \le\ \sum_{q} v_q(|D:H|).
```

In particular if the loop order has $`p'`$-part equal
to a single prime $`q`$, its inverted abelian top must
be cyclic. If the radical is elementary of rank two
at one prime, the top is cyclic regardless of the row
or core. Thus a noncyclic inverted $`C_{27}\times C_3`$
cannot compete in the original prime-exponent-one
order architecture; its genuine class-two norm question
requires a larger Hall architecture.

No assumption of central Frattini, elementary core or
block heights is used. This is an outer-architecture
exclusion, distinct from the
[actual Hall-top norm bound](prime-top-outer-reduction.md#odd-hall-top-prime-exponent-architecture).

### Faithful Hall action

Work in $`\bar D=D/N`$.
Choose a sign-stable Sylow $`p`$-subgroup $`P_0`$ there:
the odd Sylow set has a sign-fixed member, and it maps
isomorphically to $`P`$ by the normal Hall assumption.
Hence it is abelian and sign acts on it as inversion.
The kernel of its action on $`\bar B`$ is normal in $`P_0`$
and centralized by $`\bar B`$; because
$`\bar D=\bar B P_0`$, it is an ordinary normal
$`p`$-subgroup of $`\bar D`$.
It is trivial, since the preimage of a normal
$`p`$-subgroup in $`D/N`$ would be a normal $`p`$-subgroup
strictly extending $`O_p(D)`$.

The action is still faithful on the product of the
modules $`V_q=B_q/\Phi(B_q)`$. Indeed a coprime
automorphism of a finite $`q`$-group which is trivial
on its Frattini quotient is trivial: by coprime
fixed lifting the fixed subgroup maps onto the
Frattini quotient, hence is the whole group.
Apply this to every characteristic Sylow $`B_q`$.

### Reciprocal characters and the sign budget

Extend scalars in each $`V_q`$ to a splitting field of
the finite abelian $`p`$-group $`P_0`$. Its representation
is semisimple by coprimality. The sign sends the
weight of a character $`\chi`$ to that of $`\chi^{-1}`$,
because it inverts $`P_0`$. Every nontrivial character
is distinct from its inverse (the character has odd
order), so each unordered nontrivial pair contributes
at least one negative dimension. Multiplicities can
only increase that contribution: on the direct sum of
two exchanged spaces, their common dimension is the
negative dimension. Scalar extension does not change
sign dimensions.

Faithfulness of the combined action says that the
selected characters from all these pairs have trivial
common kernel; choosing one from each pair does not
alter it. Each character has cyclic image. If $`a`$
characters have trivial common kernel, then the
$`p`$-torsion subgroup $`P_0[p]`$ injects into a product
of $`a`$ cyclic $`p`$-torsion groups, so $`d(P)\le a`$.
Since there are at most $`\sum_q r_q^-`$ such pairs,
this proves the first inequality.

Finally the sharp signed index is $`|D:H|=|D:C_D(t)|`$.
Project to $`D/N`$ and apply coprime fixed lifting to
$`\bar B`$, and then within its characteristic Sylows.
For $`q\ne p`$ the resulting $`q`$-part is exactly
$`|B_q:C_{B_q}(t)|`$, since $`N,P`$ are $`p`$-groups.
This includes the negative index of its elementary
Frattini quotient, so $`v_q(|D:H|)\ge r_q^-`$.
This proves the second inequality without assuming the
projected stabilizer is already normalized.

<a id="odd-prime-index-hall-radical-q-group"></a>

## A one-prime Hall index forces a single nilpotent radical

The norm and rank preliminaries above assume a nilpotent Hall radical. The following proof replaces that hypothesis by the existence of a normal Hall subgroup.
Let an odd signed Bol envelope $`D`$ be generated by its inverted
marks and put $`N=O_p(D)`$. Suppose $`D/N`$ has a sign-stable
normal Hall $`p'`$-subgroup $`\bar B`$, and that the loop index
$`|D:H|=|D:C_D(t)|`$ has $`p'`$-part a single prime $`q`$.
Then the full $`\bar B`$ is a $`q`$-group. This conclusion
does not require nilpotency in advance, or inversion on the top.
In particular if the $`p`$-group top is abelian, it is cyclic:
its quotient is generated by inverted marks and hence sign
acts there by inversion, so the prior reciprocal-character
bound applies. Nonabelian top remains separate.

### A prime negative index in a solvable odd group

We first prove a small general lemma. For a solvable odd group
$`B`$ with an involution $`t`$ such that $`|B:C_B(t)|=q`$
is prime, the subgroup $`[B,t]`$ generated by all inverted
elements has order $`q`$.

The subgroup generated by inverted elements is normal in
$`B`$: conjugating an inverted element $`k`$ by $`b`$ gives

```math
b k b^{-1}=(b k t(b)^{-1})(t(b)b^{-1}),
```

a product of inverted elements. These are exactly the
usual coprime commutator generators: an inverted element
is obtained as $`y\,t(y)^{-1}`$ by taking its odd square
root. Choose a minimal nonzero normal subgroup $`L`$
of $`B\rtimes\langle t\rangle`$ contained in $`B`$;
it is elementary since the full semidirect group is
solvable. Coprime fixed lifting factors the negative
index through $`L`$ and $`B/L`$.

If $`t`$ acts nontrivially on $`L`$, this accounts for all
of the prime deficit, so $`t`$ fixes $`B/L`$. Every
inverted element is then in $`L`$, and the generated
subgroup is the one-dimensional negative space in $`L`$
of order $`q`$. If $`t`$ fixes $`L`$, by induction
$`[B/L,t]`$ has order $`q`$.
Every coprime commutator centralizes $`L`$: conjugation
of this normal, pointwise fixed $`L`$ by $`b`$ and by
$`t(b)`$ agrees. Thus $`A=[B,t]`$ is an extension of the
cyclic $`q`$-group by the central $`A\cap L`$, so is abelian.
Generated by inverted elements, this abelian $`A`$ is
inverted pointwise. It has order at most $`q`$, since
the negative index of a sign-stable subgroup bounds from
below the number of inverted elements in it, and the
entire inverted set in $`B`$ has size exactly $`q`$
by the usual coprime involution conjugacy count.
The quotient already has order $`q`$, proving the lemma.
The initial trivial cases are immediate.

### Signed generation kills the leftover Hall primes

In $`D/N`$, coprime fixed lifting through the Hall radical
and the $`p`$-group top gives
$`|\bar B:C_{\bar B}(t)|=q`$.
The odd Hall group is solvable by the odd order theorem,
so the lemma applies. Its normal subgroup $`[\bar B,t]`$
of order $`q`$ lies in the **characteristic** subgroup
$`K=O_q(\bar B)`$. This $`K`$ is normal in $`D/N`$ and
sign-stable, although no such assertion about
$`[\bar B,t]`$ in the full envelope is needed.

Now in $`G=(D/N)/K`$ the normal Hall radical
$`B'=\bar B/K`$ is pointwise fixed by sign.
Any inverted mark $`x\in G`$ centralizes $`B'`$:
the conjugation comparison with $`t(x)=x^{-1}`$
says $`x`$ and $`x^{-1}`$ induce the same automorphism
on $`B'`$, so the induced automorphism has order
dividing two and, also, odd order. Hence it is trivial.
The inverted marks generate $`G`$, so $`B'`$ is central.
By Schur–Zassenhaus it splits off as the direct
product factor in $`G=B'\times P_0`$ with a $`p`$-group
complement. This complement is the unique Sylow
$`p`$-subgroup (central direct product), so sign preserves it.
An inverted element has trivial component in the
pointwise fixed odd group $`B'`$.
Since the inverted elements generate, $`B'=1`$.
Therefore $`\bar B=O_q(\bar B)`$ as claimed.

The argument does not say that a reflection on the
Hall module must invert a nonabelian top: generation by
inverted elements does not force inversion of their
products. For example at the representation level an
extraspecial group generated by a cyclic shift and a
diagonal cubic-root matrix in dimension three has an
involution permuting indices $`i\mapsto-i`$: it inverts
the two generators, fixes their nontrivial scalar
commutator, and has only one negative direction.
This is a caution about outer modules, not a Bol-folder
construction. The next question would have to use the
actual stabilizer conditions to control nonabelian tops.

<a id="odd-prime-index-hall-radical-reciprocal-normal-form"></a>

## Prime-exponent-one forces the reciprocal cyclic Hall architecture

Use the preceding one-prime Hall radical theorem.
Let $`N=O_p(D)`$ in an odd signed Bol envelope generated by
inverted marks, with normally generating physical stabilizer $`H`$.
Suppose $`D/N`$ has a sign-stable normal Hall $`p'`$-subgroup
$`\bar B`$ and $`p`$-group quotient $`P`$, and the $`p'`$-part
of $`|D:H|=|D:C_D(t)|`$ is the single prime $`q`$.
If $`P\ne1`$, then necessarily:

```math
\bar B\cong C_q^2,\qquad P\text{ cyclic},\qquad
 t|_P \text{ inversion}.
```

Moreover $`P`$ acts on the two actual prime axes by a faithful
scalar character and its reciprocal, sign swaps the axes, and
the projected physical stabilizer is one prime axis semidirect
$`P`$, after ordinary normalization in $`D/N`$.
Neither abelianity of the top nor elementary Hall rank two
is assumed. In particular the reflection representation
of an extraspecial top cannot support a prime-exponent-one
physical Hall row.

### The physical Hall hyperplane

The previous theorem gives that $`\bar B`$ is a $`q`$-group
and $`A=[\bar B,t]`$ is a normal subgroup of order $`q`$.
Let $`V=\bar B/\Phi(\bar B)`$. The sign has exactly one
negative dimension there. In fact it has at most one by
coprime fixed lifting; if zero, coprime Frattini lifting
would make sign trivial on $`\bar B`$, impossible.
Choose a sign-stable Sylow $`p`$-subgroup $`P_0`$ of
$`D/N`$, projecting isomorphically to $`P`$.
Its action on $`V`$ is faithful: the kernel on $`\bar B`$
is ordinary normal $`p`$ (centralizes $`\bar B`$ and is
normal in $`P_0`$), hence trivial by $`N=O_p(D)`$;
coprime Frattini lifting makes the kernel on $`V`$ the same.

The actual image $`\bar H`$ maps onto $`P`$:
it normally generates there and a proper subgroup of
a finite $`p`$-group cannot do so.
Thus $`\bar H`$ contains a Sylow $`p`$-subgroup of $`D/N`$.
Conjugate $`\bar H`$ to place $`P_0`$ in it.
Its Hall intersection has order
$`|C_{\bar B}(t)|`$ by the sharp signed index:
all other factors of the quotient concern the core
prime $`p`$. Consequently $`\bar H\cap\bar B`$
has index $`q`$ in $`\bar B`$, contains its Frattini,
and gives a $`P_0`$-invariant hyperplane of $`V`$.
The quotient representation gives a one-dimensional
character $`\chi:P_0\to\mathbb F_q^\times`$.
This is a consequence of the actual physical Hall
row, not a character search.

### The quotient character cannot be trivial

Under the coprime $`P_0`$-action, decompose $`V`$
as $`V^{P_0}\oplus[V,P_0]`$, stable under sign
because sign normalizes $`P_0`$.
The quotient of the envelope with this Hall
action trivialized is the direct product
$`V^{P_0}\times P_0`$.
It is generated by images of inverted marks.
Therefore sign inverts $`V^{P_0}`$: its inverted
components must generate that abelian direct factor.
If $`V^{P_0}\ne0`$ it uses the entire one-negative
budget, so sign is identity on $`[V,P_0]`$.
Every inverted element of $`P_0`$ then acts
trivially there: its operator equals its own inverse
under the identity sign, and has odd order.
The projected inverted marks generate $`P_0`$,
so $`P_0`$ acts trivially on all of $`V`$,
contradicting faithfulness for $`P\ne1`$.
Hence $`V^{P_0}=0`$; by coprime semisimplicity
the one-dimensional quotient character is nontrivial.

### Two reciprocal axes and no remaining radical

The nontrivial character $`\chi`$ occurs as a submodule.
Its sign partner has character $`\chi\circ t`$;
on each inverted element of $`P_0`$ this agrees with
$`\chi^{-1}`$. These elements generate $`P_0`$,
so the partner is exactly $`\chi^{-1}`$.
They are distinct since the character is nontrivial
of odd order. Their exchanged lines already use
the one negative direction. The sum of their
isotypic components has just one copy each for
the same reason, and its sign-stable semisimple
complement has trivial sign. As before every
inverted element acts trivially on this complement,
so the complement is $`P_0`$-fixed; it is zero.
Thus $`V`$ is precisely the two reciprocal lines.
Faithfulness means $`\chi`$ embeds $`P_0`$ into
$`\mathbb F_q^\times`$; the top is cyclic and sign
inverts it.

The order-q subgroup $`A=[\bar B,t]`$ projects
onto the actual negative line of $`V`$.
Its conjugates under $`P_0`$ are normal order-q
subgroups of $`\bar B`$. Distinct such subgroups
commute, since their commutators lie in their trivial
intersection; their joint subgroup is elementary.
Their images span $`V`$, since the negative line
has nonzero components in both distinct character
lines and the $`P_0`$-module is semisimple.
By the Frattini property these conjugates generate
all of $`\bar B`$. Hence $`\bar B=V\cong C_q^2`$.
The two character lines are now actual axes,
and sign exchanges them. A $`P_0`$-invariant Hall
hyperplane is one of the two lines, so the
normalized projected $`\bar H`$ is that axis
semidirect $`P_0`$, as required.

This result concerns the normal Hall architecture;
it does not assert such a Hall layer must exist
for every finite simple proper Bol loop of two-prime
order, nor does it determine the possible cyclic
orders or their stabilizer charts.


<a id="automatic-hall"></a>

## The normal Hall architecture is automatic


Let $`D,H,t`$ be an odd solvable signed Bol
envelope generated by inverted marks, with normally generating
physical stabilizer $`H`$ and the sharp signed index.
Suppose the loop order is $`p^a q`$ for distinct odd primes
$`p,q`$, $`a\ge1`$. Then $`N=O_p(D)`$ has a canonical outer
normal Hall layer:
```math
D/N=C_q^2\rtimes C_{p^k},\qquad k\ge1.
```
The cyclic top acts faithfully by reciprocal scalars, sign
swaps the two axes and inverts the top, and the normalized
projected physical stabilizer is one axis semidirect the top.
In addition, under the strict signed cuts,
```math
p^k+k\le a.
```

### Prime support of a mark-generated solvable group

More generally, if a finite odd solvable group $`G`$ is generated
by its inverted elements for a sign involution, every prime of
$`|G|`$ divides $`|G:C_G(t)|`$. Prove this by induction using a
nonzero minimal normal subgroup $`A`$ of $`G\rtimes\langle t\rangle`$
contained in $`G`$; it is elementary of some prime order power.
The quotient is generated by images of inverted elements and
its fixed index divides the original by coprime fixed lifting.
Thus all its prime divisors are in the original index support.
If the prime of $`A`$ is outside this support, $`t`$ fixes $`A`$
pointwise. In this event every inverted generator centralizes
$`A`$: its conjugation and inverse conjugation agree there,
so its action is simultaneously of odd order and order at most
two. Hence $`A`$ is central. Its prime is absent in the quotient
by induction, so it is a central normal Hall subgroup.
Schur–Zassenhaus gives the direct product of $`A`$ and a
complement of coprime order. That complement is unique
(the elements of order coprime to $`|A|`$ in this direct product),
so sign preserves it. Inverted elements have no component in
the pointwise fixed odd $`A`$, contradicting generation.
This completes the induction. The reverse inclusion of supports
is immediate since the index divides the group order.
The lemma applies to every sign-stable quotient as well.

### The outer Hall layer

Put $`\bar D=D/N`$. It has prime support contained in $`\{p,q\}`$
by the preceding lemma, has no normal $`p`$-subgroup, and its
fixed index still contains a single factor $`q`$ by coprime
fixed lifting through $`N`$. In the solvable $`\bar D`$, its
Fitting subgroup therefore equals $`S=O_q(\bar D)`$.
It cannot be pointwise fixed by $`t`$: otherwise, just as in
the lemma, every inverted generator centralizes it.
The self-centralizing Fitting theorem would give
$`\bar D=S`$, which then would itself be pointwise fixed,
contrary to its factor $`q`$ in the index.
Hence $`S`$ uses the unique factor $`q`$ of the fixed index.
The quotient $`\bar D/S`$ has fixed index a power of $`p`$,
is generated by inverted elements, and is solvable.
The support lemma makes it a $`p`$-group.
Thus $`S`$ is a normal Hall $`p'`$-subgroup, with no
normal-Hall hypothesis needed in advance.

Its quotient top is nontrivial: if $`\bar D=S`$ were a
$`q`$-group, the actual $`\bar H`$ would have index $`q`$
by the sharp index and the $`p`$-power core. It would
be proper in this $`q`$-group, and could not normally
generate it because a proper subgroup lies in a normal
maximal subgroup. Thus the top $`P`$ is nontrivial.
Apply the [reciprocal normal form](#odd-prime-index-hall-radical-reciprocal-normal-form)
to get the asserted $`C_q^2\rtimes C_{p^k}`$, including
the actual normalized projected stabilizer and sign.

### The order bound

The action of the actual $`q`$-complement $`B`$ on
$`N/\Phi(N)`$ is nontrivial. Otherwise coprime Frattini
lifting makes it trivial on $`N`$. In that case an
actual sign-stable $`B`$ would be normal in $`D`$:
it centralizes $`N`$ and is normalized by the
normalizer of $`B`$, which surjects onto $`\bar D`$ by
complement conjugacy. The actual physical $`H`$ contains
a subgroup over its projected prime axis; if a conjugate
of that lift were needed, normality of $`B`$ puts it
in the same $`B`$. Thus $`|H\cap B|\ge q=|C_B(t)|`$,
violating the strict signed cut. This also excludes $`N=1`$
under the cut hypotheses.

Over a splitting field a nontrivial weight on this elementary
Frattini quotient has top orbit of length $`p^k`$, since at
least one of its two coordinates is nonzero and its multiplier
has exact order $`p^k`$. If the orbit is axial, sign swaps
it with an orbit on the other axis, costing at least $`p^k`$
negative dimensions. For mixed orbits one must check an
additional case: sign may reflect an individual orbit.
For a reflected orbit, its negative dimension is at least
$`(p^k-1)/2`$, but the Frobenius returns require $`p^{2j}=1`$
modulo $`q`$. Thus whenever $`\mathrm{ord}_q(p^2)\ge3`$,
there are at least three Frobenius-translated geometric
orbits and their sign partners; this costs at least $`p^k`$.
If $`\mathrm{ord}_q(p^2)\le2`$, then $`q\mid p^4-1`$.
Since $`q\equiv1\bmod p^k`$, this last case is impossible
for $`k\ge2`$: any odd prime dividing $`p^4-1`$ divides
$`p-1,p+1`$, or $`p^2+1`$; the first two factors are too
small, and if it divides $`p^2+1`$ and is $`1\bmod p^2`$,
it must equal $`p^2+1`$, which is even. For $`k=1`$,
the same conclusion holds: a prime $`q\equiv1\bmod p`$
dividing $`p-1`$ or $`p+1`$ is impossible for odd $`p`$;
if it divides $`p^2+1`$, its complementary factor is
also $`1\bmod p`$, as the product is $`1\bmod p`$.
Both are positive; the latter factor is $`>1`$ unless
$`q=p^2+1`$, which is even. Their least possible
values $`p+1`$ yield a product $`>(p^2+1)`$.
Thus $`\mathrm{ord}_q(p^2)\ge3`$ in all cases.
For odd $`p^k\ge3`$, $`3(p^k-1)/2\ge p^k`$.
So either type forces at least $`p^k`$ core negatives.
The top contributes $`k`$ to the $`p`$-exponent of the
loop index by inversion and fixed lifting. This proves
$`p^k+k\le a`$.

This theorem identifies the group architecture for this
order pattern; it does not automatically identify the core
or prove the numerical census for smaller cyclic tops.
