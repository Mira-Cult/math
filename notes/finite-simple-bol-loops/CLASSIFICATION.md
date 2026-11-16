# Classification map

## What would count as a classification?

The desired result should give explicit construction data; prove that every
finite simple Bol loop occurs; determine when two data sets give isomorphic
loops; and explain the structural content of the surviving data. These are
separate obligations. An existence theorem does not prove exhaustion. A finite
admissibility test does not prove that the admissible parameters have been
understood. An isotopy classification is not an isomorphism classification.

Efficient duplicate-free generation is a useful later objective, not the present
acceptance criterion. No constant-delay or polynomial-delay claim is intended.

## Classical boundary

Associative simple loops are finite simple groups. Nonassociative finite simple
Moufang loops are the Paige loops, by the finite simple Moufang classification.
These are established starting points, not results of this project.

The remaining target is finite simple **proper** Bol loops. Important routes
through that target include:

| Route | What must be controlled | Main pitfall |
| --- | --- | --- |
| Bruck loops and their isotopes | Radical, quotient, section, stabilizer, simplicity, and isotope-to-isomorphism data | Restricting to exponent two, one quotient factor, or elementary radicals misses possibilities. |
| Exact-factorization constructions | Admissible factorizations, their loop constructions, and redundancy of presentations | This is a source of examples, not an established exhaustive description of all proper Bol loops. |
| Odd-order canonical envelopes | Solvable group data, the distinguished inversion, stabilizers, and strict transversality | Passing to a group quotient need not produce a quotient loop. |
| Even-order non-Bruck-isotopic loops | Interactions between radical and nonsolvable quotient, plus valid sections | A group satisfying numerical necessary conditions need not support a Bol loop. |
| Multiplication-group restrictions | Which permutation actions actually admit the required translations | Confusing `Mlt` and `LMlt`, or necessary action restrictions with sufficient constructions. |

These are overlapping research routes, **not a proved disjoint exhaustive tree**.
For instance, a particular construction may be both an exact-factorization loop
and a G-loop. An example outside two known classes establishes a missing route;
its large order alone does not make it sporadic or exceptional.

## How to use a family-level result

For every proposed family or parameterization, record five answers:

1. **Input:** exact hypotheses and parameter domain.
2. **Output:** order, properness, simplicity, and any isotopy properties proved.
3. **Exhaustion:** exactly which subclass is covered, if any.
4. **Equivalence:** the isomorphism relation on parameters, including all allowed changes of basis and presentation.
5. **Evidence:** proof imports, source revision, tests, and scoped reviews.

A general scheme with arbitrarily large parameters and expensive tests may still
be useful. Describe it as such rather than advertising it as a small list of
families or an efficient enumerator. If a parameter problem contains arbitrary
matrix-pair equivalence, that constrains the kind of normal form one should seek;
it does not alone prove a computational complexity lower bound.
