# Maintaining “no adjacent aa” with unary existential updates

*Mira Cult*

A dynamic program can maintain whether a word has no adjacent pair of a’s using only unary auxiliary relations, answer bits, and existential first-order update formulas. The trick is to store a counter as either a prefix of the domain or its complement, switching the interpretation when the counter increases rather than decreases.

This gives a positive answer to Research Index problem 0263 and refutes the explicit nonmembership assertion highlighted in [Conjecture 37 of Barloy, Tschirbs, Vortmeier and Zeume](https://arxiv.org/html/2601.18429v1#S6). It does not give an algebraic characterization of the whole dynamic class.

## Model and theorem

The domain is a fixed finite linear order. All positions start empty, and an update replaces the symbol at a single position with a, b, or ε. The represented word ignores ε, so two occupied positions can be adjacent in the word without being consecutive in the domain. Formulas see the new input and the old auxiliary structure. Initialization is first-order; all update formulas have an existential prefix and a quantifier-free matrix, with negations of atoms allowed. No successor, arithmetic, or auxiliary relation of arity two is used.

**Theorem.** In this model there is a single unary-auxiliary existential program for “no adjacent aa”, valid for every domain size and after every finite sequence of updates.

## The count changes locally

Let k count the adjacent aa pairs. At the changed position i let L(i) and R(i) say that the nearest occupied position strictly to the left or the right carries an a. Both are false when their respective neighbor does not exist. Treating their truth values as 0 or 1, the local contribution is L(i)+R(i) when the symbol at i is a, zero when it is b, and L(i)R(i) when it is ε. All other consecutive pairs are unaffected.

Thus the true count change δ is the difference between the new and old local contributions and belongs to {−2,−1,0,1,2}. The program stores copies of the input letter predicates, copied from the new input by each update. With these copies and the decoded neighbor flags, each test Dδ for the corresponding count change is quantifier-free: it is just a Boolean case split in two bits and the old and new symbols.

## Maintaining the nearest occupied letter

We give the right-hand flags; the left-hand rules reverse the order. Store a physical unary predicate R* and a bit p. The logical flag R(x) is R*(x) when p is true and its negation otherwise. Both polarities of R(x) can therefore be read quantifier-free. Initially R* is empty and p is true.

Write n = R(x), m = R(i); when x < i let Eₐ and Eᵦ say that the open interval (x,i) contains an a or a b, respectively. These are existential tests and the interval excludes the update, so either input version gives the same answer there. The physical update is:

| Action | New p | R*(x) for x ≥ i | R*(x) for x < i |
| --- | --- | --- | --- |
| Write a | false | ¬n | ¬n ∧ Eᵦ |
| Write b | true | n | n ∧ Eₐ |
| Erase a | true | n | n ∧ (m ∨ Eₐ) |
| Erase b | false | ¬n | ¬n ∧ (¬m ∨ Eᵦ) |
| Erase an empty slot | true | n | n |

For a write at x < i, the new flag depends on the first occupied position between x and i if there is one, and otherwise on the new letter at i. For example, after writing a, the resulting flag is false exactly when the first intervening letter is b. This is equivalent to ¬n ∧ Eᵦ: if a b intervenes, the old first occupied position is also in the interval. The b row follows by the same reasoning.

On erasing a, a previously false flag stays false. A previously true flag remains true if an a intervenes, and otherwise takes the value R(i). On erasing b, apply the corresponding argument to the false flag; a missing neighbor counts as “not a” here. For x ≥ i there is no semantic change. Every interval predicate in the physical formulas is positive. This is the complemented-relation technique from [Example 4](https://arxiv.org/html/2601.18429v1#S2.SS1), with the overwrite and empty-slot cases included.

## A counter with two representations

Store the first k positions of the fixed order in a unary predicate T, represented by a physical set C and a bit q. When q is true, C represents T directly; otherwise C represents its complement. Initially C is empty and q is true.

- **Decrease by d, where d is 1 or 2:** Set q true. Put x in the new C if there are d distinct old T-points strictly above x. If x has rank r, this holds exactly when r ≤ k−d.
- **Increase by d:** Set q false. Put x in the new C if there are d distinct old non-T points strictly below x. There are max(r−1−k,0) such points. The test holds exactly when r > k+d, giving the complement of the new prefix.
- **No change:** Set q true and copy the decoded T.

The numerical distances are only for the proof. Each test has at most two witnesses and uses just comparisons with x, distinctness, and the old decoded membership flags.

To maintain the answer bit, first-order-initialize immutable unary marks for the second and third domain positions, where present. On decrease by d, the new count is zero exactly when the old count is d, since the change cannot make it negative. This is tested by existentially finding the (d+1)-st position outside the old prefix. The mark always exists in this case: k ≥ d adjacent pairs require at least d+1 occupied positions. On an increase, output false. On no change, copy the old answer bit. The initial answer is true, including on the empty domain, where there are no updates.

The branch tests are quantifier-free. Disjunctions of the displayed formulas can be put in existential prenex form by renaming witnesses and filling unused slots with the supplied update position i. The neighbor flags, counter and answer are therefore correct by induction after every update.

## Other fixed adjacency constraints

The same construction works for any fixed finite alphabet and any fixed forbidden set of ordered adjacent pairs. Maintain a nearest-neighbor flag for each letter, using the same table for that letter versus all other occupied letters. The contribution at i is now the number of forbidden pairs across the new left and right joins, or the single bridge across i when it is empty. The change still lies between −2 and 2, so the same counter and zero test apply. This does not cover arbitrary longer forbidden substrings.

## Reference and verification

Corentin Barloy, Felix Tschirbs, Nils Vortmeier and Thomas Zeume, *Algebraic Characterizations of Classes of Regular Languages in DynFO*, STACS 2026, [DOI 10.4230/LIPIcs.STACS.2026.9](https://doi.org/10.4230/LIPIcs.STACS.2026.9), §2.1 and §6. The published complement program is the baseline, not the new counter. The present argument uses negation of auxiliary atoms, and does not refute results about positive existential updates.

Run `python3 check.py` for an exhaustive transition check on orders 0 through 7, including both old polarity bits. The proof above covers all orders. No external referee review or formal verification is claimed.

AI tools assisted the proof development and checks. The source packet does not identify the models reliably enough to credit specific versions.
