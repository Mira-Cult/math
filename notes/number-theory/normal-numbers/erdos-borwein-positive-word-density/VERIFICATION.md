# Verification and sources for the positive-density theorem

[The theorem](../0002-erdos-borwein-positive-word-density.md) and [proof outline](proof.md) are accompanied by the main analytic estimates. This is a conventional mathematical result with internal proof checks. It is not a formal verification or a claim of external referee acceptance.

## Scope of the checks

Two nonauthor internal checks reviewed the comparison on the actual prime intervals and the extension from a midpoint for the mixed length-two words to an arbitrary fixed word. They checked the order of the sieve cutoffs, the lattice normalization in the marked local comparison, the source of the short-interval prime estimate, the averaging order for adaptive cofactors, and the use of the same avoidance probability in the conditional numerator and denominator. The arbitrary-word check also verified the exact midpoint, the second-moment bound by genuine incidences, and the strict cylinder margin. The observed-start probability comes from Cauchy–Schwarz, not from an approximation of binary carries.

- [Adaptive marker count](adaptive-marker-count.md) and [fixed-word incidence estimates](fixed-word-incidences.md).
- [Weighted local comparison](weighted-local-comparison.md) and [conditional isolation](conditional-isolation.md).
- [Size-biased tail](marked-tail.md), [integrated deficit estimate](integrated-deficit.md), and [valuation atom bound](valuation-atom-bound.md).

The supporting notes retain the main estimates and their mathematical lineage. They are not a line-by-line expansion of every reused comparison or of the published sieve theorems.

## References

- M. N. Huxley and H. Iwaniec, [*Bombieri’s theorem in short intervals*](https://doi.org/10.1112/S0025579300006069).
- A. Perelli, J. Pintz and S. Salerno, [*Bombieri’s theorem in short intervals*](https://www.numdam.org/item/ASNSP_1984_4_11_4_529_0.pdf), pp. 529–530, especially equation (2) and its stated exponent ranges.
- J. M. Campbell, [*On the binary digits of the Erdős–Borwein constant*](https://arxiv.org/abs/2605.24160v1), for infinite occurrence of the word `11`.

Research-source revision: `3d6095d99e07b71fc112d538c845d2cf6c6da80d`. The public release contains only the positive-density argument and its supporting estimates. The result makes no priority claim beyond the cited comparisons.
