# Power-of-two counting captures uniform TC⁰

[Paper (PDF)](paper/power-of-two-counting.pdf) · [LaTeX source and build instructions](paper/README.md)

**Theorem.** On every nonempty finite linear order $`\{0,\ldots,n-1\}`$, the relation $`ab=c`$ is definable by one first-order formula using only order and the unary quantifier $`C_E`$ that tests whether a definable set has power-of-two size. The formula uses at most three nested occurrences of $`C_E`$. Consequently this logic captures **DLOGTIME-uniform TC⁰** on nonempty finite ordered words.

Here $`E=\{1,2,4,\ldots\}`$, so the empty set fails the test. Truncated multiplication means ordinary equality $`ab=c`$ for three elements of the *original* order, not multiplication modulo its size and not multiplication inside an enlarged universe. This resolves the expressiveness question of [Hella, Kontinen, and Luosto, §6](https://doi.org/10.1145/3750044).

**Open refinement:** Can exact multiplication be expressed with nesting depth two? Depth one is impossible even with truncated addition supplied. The theorem does not require the upper bound of three to be optimal.

## The key idea: a shift is a count

Suppose we know the set bits of a small number $`q`$. To express $`q`$ shifted left by $`e`$ places, send each bit of index $`j`$ to the weight $`p=2^{e+j}`$. The half-open interval $`[p,2p)`$ has length $`p`$, and the intervals for distinct powers of two do not overlap. Their union therefore has size equal to the shifted number.

There is one endpoint exception. If $`P`$ is the greatest power of two in the order, the interval $`[P,2P)`$ may not fit. Count just the lower intervals, then add $`P`$ if that bit is present. For example, to shift five left by one in $`\{0,\ldots,10\}`$, the desired weights are 2 and 8. Count the two elements in $`[2,4)`$, then add 8. Neither a 16-element order nor a point representing 16 is needed.

## The construction

### 1. Count and index powers

Write $`\mathrm{Eq}(A,B)`$ for the equicardinality test on two unary definable sets. It can be expressed by $`C_E`$ with one additional layer over the depths of the sets' defining formulas. The [paper, §2](paper/power-of-two-counting.pdf) gives a formula template: compare small sets by padding both from a common exterior and looking for the first discrepancy at a power-of-two size, then partition the order into eight small pieces and compare the summed counts.

Truncated addition $`a+b=c`$ compares $`[a,c)`$ with $`[0,b)`$, requiring $`a\le c`$. Power membership $`p\in E`$ is the test $`C_E x\,(x<p)`$. To express $`p=2^i`$, also compare the set of powers strictly below $`p`$ with $`[0,i)`$. Thus addition and power membership have depth one, and indexed powers have depth two.

### 2. Get exact small products

First define a sound but space-limited product $`xy=z`$. If $`x,y>0`$, choose the least power $`p\ge x`$. Use $`0`$ and all sums of at most two distinct powers of two at least $`p`$ as possible starts of length-$`x`$ intervals. All the starts are distinct multiples of $`p`$. Select an initial portion of them by a cutoff, require exactly $`y`$ selected starts, and require that the last interval fits. The disjoint union of those intervals has size $`z`$ exactly when $`xy=z`$. These are depth-two tests: membership uses power tests and addition, and the union count adds one layer. Zero factors are checked separately.

This works especially well when $`y`$ is small. With $`t`$ available bit positions starting at $`p`$, there are $`1+t(t+1)/2`$ starts no larger than $`p(2^t-1)`$. A true product with its arguments in the order is therefore recognized if there are at least $`y`$ such starts and $`p(2^t-1)+x\le n`$.

To check $`ab=c`$, let $`u=\max(a,b,c)`$, let $`l`$ count the powers of two at most $`u`$, and set $`K=2l+2`$. Verify the product modulo every integer $`2\le m\le K`$. The residue of $`a`$ modulo $`m`$, for example, is witnessed by $`a=vm+r`$ and $`0\le r<m`$, using the interval product for $`vm`$. Multiply the two input residues, then reduce the result modulo $`m`$ in the same way. In these interval products the second operand can always be chosen at most $`K`$. Successful congruence checks force equality because $`|ab-c|<2^{2l}`$ for positive factors, while $`\operatorname{lcm}(1,\ldots,K)\ge 2^{K-1}`$. The bound follows from [Farhi's binomial-coefficient identity](https://arxiv.org/abs/0906.2295). Congruence tests and auxiliary witnesses are combined in ordinary first-order scope, so the depth stays two.

For the range needed below, let $`2^h`$ be the largest power in the domain, $`k=\lfloor h/4\rfloor`$, and $`B=2^k`$. If $`n\ge65{,}537`$ then $`k\ge4`$. When the three arguments are below $`B^2`$, we have $`K\le4k+2`$. The largest width in any residue calculation is bounded by $`2B^2`$, since even the product of two residues is at most $`(4k+2)^2\le2B^2`$. With $`t=2k-2`$ positions, there are at least $`4k+2`$ starts, and the last interval fits: its right endpoint is at most $`2B^2\cdot 2^t=2^{4k-1}<n`$. This pays for all genuine witnesses and proves completeness on the required range.

### 3. Read a bit and shift it

For $`q<B^2`$, bit $`j`$ is set if $`q=tp+r`$ with $`p=2^j`$, $`t>0`$ odd, and $`0\le r<p`$. This is a depth-two formula, using indexed powers, the small product above, and addition. When a bit is set, all these numerical witnesses are at most $`q`$, so the small-product guarantee applies.

For a shift by $`e`$, first require that **every** set bit has its target index $`e+j`$ and target weight in the domain. Locate each lower interval $`[p,2p)`$ by addition. Membership in their union uses the depth-two bit test and indexed powers in parallel. The outer equicardinality test counts the union in one additional layer. Add the greatest power if it was selected. This is exact on the guarded range: an unavailable weight or final overflow makes the test fail, whereas a shift of zero always returns zero.

### 4. Assemble the full product

Five base-$`B`$ digits represent every element of the order since $`B^5\ge2^{h+1}\ge n`$. Witness the digits of each input and check the representations by shifts and additions. The 25 products of pairs of digits are below $`B^2`$; get them using the depth-two small-product test. Shift each by its base-$`B`$ place and add the results to obtain $`c`$. If the true product fits, every nonnegative term and partial sum fits. All 25 operations form one fixed formula, with no new counting layers. The finitely many orders below the cutoff are handled by a pure-order disjunction on size and positions.

## What follows

Order, multiplication, and Härtig equicardinality capture DLOGTIME-uniform TC⁰ on nonempty ordered words by [Hella, Kontinen, and Luosto, §2](https://doi.org/10.1145/3750044). Conversely, that arithmetic logic can compare a nonempty set to the prefix ending at $`v`$ and ask whether $`v`$ consists of all ones in binary (including zero for a prefix of size one). This tests $`C_E`$ without representing $`n`$ as a domain element. Thus both inclusions hold.

For the depth-one lower bound, relativize a candidate formula to $`[0,n)`$ in the natural numbers. The child of each $`C_E`$ would be a Presburger formula, whose exact unary cardinality is Presburger-definable by [Schweikardt](https://arxiv.org/abs/cs/0211022). So the entire formula would translate to [decidable Presburger arithmetic with a power-of-two predicate](https://doi.org/10.4230/LIPIcs.ICALP.2023.112). Existentially choosing $`n`$ would then define full natural-number multiplication there, which is impossible. At depth two, the outstanding problem is to remove the extra counting layer in the shift or obtain an alternative exact same-order construction.

## Acknowledgment and verification

OpenAI models assisted in developing the proof, drafting the exposition, and checking the argument, under Mira's guidance. The proof received a separate nonauthor automated proof check, including the endpoint and nesting bounds. The proof is conventional mathematics and does not rely on computational experiments, formal verification, or external referee review.
