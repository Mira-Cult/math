# Normal numbers and digit expansions

This workspace studies two complementary questions: how complex the digits of a fixed real number must be, and how to construct new digit streams with prescribed statistical behavior.

## Joint digit switches in coprime bases

A **switch** is an adjacent pair of unequal digits within one expansion. For example, `10011` has two switches. Count the switches separately in the first $N$ fractional digits in base 2 and in base 3, then add the counts.

For every irrational real number, the combined count is at least a positive constant times $\log N\log\log N$ for every sufficiently large $N$. The constant is independent of the number; the cutoff may depend on it. The same result holds for any fixed pair of coprime integer bases.

**[Read the theorem and full proof](0001-joint-digit-switches.md).** The proof analyzes sparse windows in the two expansions and uses the quantitative Subspace Theorem to bound how often such windows can occur.

### What remains open

This bound does not choose a base in which the switches are frequent, prove positive switch density, or prove normality of any particular irrational number. Natural next questions are whether the joint lower bound can be increased and what fails when the bases share a prime factor.

## Erdős–Borwein: positive density of every fixed word

Every fixed binary word occurs in the Erdős–Borwein constant with positive lower density. More precisely, for each fixed $a>7/12$, it occupies a positive proportion of starts in every sufficiently late window of length $H$ between $N^a$ and $N$, with a constant depending on the word and $a$.

**[Read the theorem](erdos-borwein-positive-word-density/README.md).** This gives no limiting frequency and does not prove binary normality.

## Stoneham series: joint normality

Certain Stoneham and related series at a common argument are jointly normal in their defining base. Every nontrivial rational linear combination is therefore normal in that base. The same proof method gives a denominator criterion for generalized Stoneham series and a normality theorem for series indexed by integers built from a fixed set of primes.

**[Read the statements and proofs](stoneham-joint-normality.md).** This does not establish normality of nonlinear polynomial values of Stoneham constants.

## Normal Dovetails: constructing normal digit streams

The [Normal Dovetails proof and replay packet](normal-dovetails/README.md) constructs a normal stream in a fixed base by concatenating complete fractional prefixes of values of a nonpolynomial real D-finite function at suitable rational inputs. The proof controls every output prefix. This is a theorem about the constructed stream, not about normality of the original function values.
