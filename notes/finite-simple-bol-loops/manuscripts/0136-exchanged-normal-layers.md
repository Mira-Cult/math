# Exchanged normal layers in simple Bol loops

**Mira Cult**

A normal layer of the left multiplication group can carry two factors exchanged by the marked inversion. This symmetry fixes the size of each nonempty translation fiber. In a simple loop, the resulting multiplicity restricts the projected point stabilizer and rules out a coprime quotient when the fiber size is even.

## Hypotheses and statement

Let $`Q`$ be a finite simple proper left Bol loop: simplicity means that the only normal subloops are the trivial subloop and $`Q`$, and proper means non-Moufang. Use its original faithful generated folder with left translation group $`G`$, identity stabilizer $`H`$, and set $`K`$ of left translations. The marked-extension hypotheses used here are these: $`E=G\rtimes\langle\tau\rangle`$, the mark $`\tau`$ inverts each element of $`K`$, and $`\Lambda=\tau K`$ is an $`E`$-conjugacy-invariant set of involutions. These are the canonical left Bol folder hypotheses; the proof below also applies to any such marked folder realizing a simple loop. For the underlying folder framework see [Nagy's construction paper](https://dml.cz/handle/10338.dmlcz/119721) and the [involution-support description](../update-2026-11-16/manuscripts/radical-free-involution-support.md).

Let $`1\ne N\lhd E`$ with $`N\le G`$, and assume either:

1. $`N=B\times C`$ for normal subgroups of $`G`$ with $`C=\tau B\tau^{-1}`$; put $`D=|B|`$.
2. $`N=T^{2b}`$ for a nonabelian simple group $`T`$, and every selected mark exchanges the simple factors of $`N`$ in pairs; put $`D=|T|^b`$. The pairing can depend on the mark.

Write $`L=G/N`$, $`J=HN/N`$, and let $`\bar K`$ be the image of the translations in $`L`$. Then each nonempty translation fiber has size $`D`$, and each left coset of $`J`$ in $`L`$ contains exactly

```math
r=\frac{D}{|H\cap N|}

```

distinct members of $`\bar K`$. In particular $`r`$ is an integer dividing $`D`$ and, for $`N<G`$, it is at least two.

For a proper layer, if $`L`$ has odd order then $`r`$ divides $`|L|`$ as well. More generally, if $`J`$ has odd order, then every selected quotient mark $`x`$ satisfies

```math
r=[J\cap xJx:C_J(x)].

```

Consequently, if $`D`$ is even, the actual projected stabilizer $`J`$ has a common prime divisor with $`D`$, regardless of the order of $`L`$. In particular $`|L|`$ cannot be coprime to $`D`$.

## Proof

**Translation fibers.** Fix an actual mark $`x\in\Lambda`$. In the first case every mark exchanges $`B`$ and $`C`$, since every element of $`G`$ normalizes both. In coordinates identified by $`x`$, an involution in $`xN`$ has the form $`x(t,t^{-1})`$. Conjugating $`x`$ by elements of the first copy produces all of these; there are $`D`$. In the second case the same calculation applies independently to every pair and gives $`D`$ again. In either case all of them are selected by conjugacy invariance. Left multiplication by $`\tau`$ identifies these marked fibers with fibers in $`K`$.

**Multiplicity and strictness.** A left coset of $`HN`$ contains $`[N:H\cap N]`$ left cosets of $`H`$. Every such coset contains one translation, and a projected translation accounts for exactly $`D`$ of them. Since $`|N|=D^2`$, the claimed count follows.

If $`HN<G`$ and $`r=1`$, the projection to $`L/J`$ defines a loop quotient. To see this directly, represent a point of $`Q`$ by the left coset $`kH`$ of its unique translation $`k`$. The product of points represented by $`kH`$ and $`k'H`$ is represented by $`kk'H`$. The same rule on projected cosets is well defined because each has a unique representative in $`\bar K`$; both translations of the induced product are surjective, by the loop property upstairs, and hence bijective on the finite quotient. Its kernel is nontrivial since $`N`$ cannot lie in $`H`$ by faithfulness, and is proper because $`HN<G`$. This contradicts simplicity. If $`HN=G`$ and $`r=1`$, then $`\bar K=\{1\}`$, contrary to generation unless $`N=G`$. This proves strictness for proper layers in both cases.

**Odd-order quotient.** The involutions outside $`L`$ in $`E/N`$ are conjugate under $`L`$ by Sylow conjugacy. The marked set contains the image of $`\tau`$ and is conjugacy invariant, so it consists of the entire outside involution class. Counting its elements in two ways gives $`r=|J|/|C_L(\bar\tau)|`$. In particular $`r`$ divides $`|L|`$.

**Odd stabilizer.** The marks in $`xJ`$ form one orbit of $`J\cap xJx`$. Indeed, for any other mark $`y=xj`$ in that coset, $`x`$ inverts $`j`$. Since $`j`$ has odd order, it has a square root $`h`$ in its own cyclic subgroup. Then $`h\in J\cap xJx`$ and $`h^{-1}xh=y`$. Conversely this intersection conjugates $`x`$ inside $`xJ`$, preserving selection. The orbit has exactly $`r`$ marks by the coset count (left multiplication by $`\bar\tau`$ maps a translation coset to the marked coset). Its stabilizer is $`C_J(x)`$. This proves the index formula and the common-prime claim: if $`J`$ is odd use the divisor $`r\ge2`$, and if both $`J`$ and $`D`$ are even use 2.

## Scope and review

This is a restriction on a specified normal layer, not a list of the possible layers or a classification of Bol loops. It uses the actual projected stabilizer. In the simple-factor case the premise is on every selected mark, not only on $`\tau`$; allowing fixed coordinates can give nonuniform fiber sizes.

AI models assisted the proof and its mathematical review under Mira's guidance. Two independent OpenAI GPT-6.1 Terra reviews checked the counted fibers and proper-layer deductions at research revision `7a2f3b2b` and the odd-stabilizer extension at `b9f4ff95`. Those scoped reviews retain the original folder and inversion hypotheses. The public claim identifier is 0136; its internal source is a continuation of problem 0323, claim C0010.
