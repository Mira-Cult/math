# Reproducible finite checks

The scientific programs below are byte-identical copies of the sources
identified in [VERIFICATION.md](../VERIFICATION.md). Their historical
manuscript filenames in docstrings are retained to preserve that identity;
the public mapping is below. The Python programs use only the standard
library. Python 3.11 or newer is sufficient; the C scan needs a C compiler
and the system math library.

## Current uniform-interaction checks

### Uniform bounds with unbounded interaction size

All ten programs below use Python 3.11+ and the standard library. The observed
runs used Python 3.12.14. From the repository root:

```sh
python notes/combinatorics/fourier-entropy-influence/code/check_directional_integer_factors.py
python notes/combinatorics/fourier-entropy-influence/code/check_affine_forest_entropy.py
python notes/combinatorics/fourier-entropy-influence/code/check_recursive_point_interference.py
python notes/combinatorics/fourier-entropy-influence/code/check_one_point_product_interference.py
python notes/combinatorics/fourier-entropy-influence/code/check_positive_support_reduction.py
python notes/combinatorics/fourier-entropy-influence/code/check_pointed_envelope_review.py
python notes/combinatorics/fourier-entropy-influence/code/check_marked_set_closure.py
python notes/combinatorics/fourier-entropy-influence/code/check_marked_set_rare_leaf_improvement.py
python notes/combinatorics/fourier-entropy-influence/code/check_approximation_barriers_for_marked_products.py
python notes/combinatorics/fourier-entropy-influence/code/check_cyclic_partition_obstruction.py
```

The directed checker verifies actual Boolean Walsh transforms on 12 and 16
variables, exact formulas for odd majority-core sizes through nine, 1,044
complement-cylinder factors, 100 integral-power factor tensors (seed
20261117), rare-point cores through twelve variables and the multi-atom
shaving obstruction. The independent reviewer also ran the optional
`--boolean-ell 5` check, constructing the 20-variable truth table and all
1,048,576 integer Walsh coefficients. Every assertion is exact.

The affine checker enumerates all unlabeled connected tree shapes through
four vertices, all roots, nonroot fields -2..2, nonzero couplings in
{-2,-1,1,2}, and seven root fields -3..3. It performs 456,686 own partition
bounds and 2,740,122 cross comparisons, including the product comparison
on every nontrivial tree. Its 600 seeded trees on five through ten vertices
add 4,200 own and 25,200 cross comparisons. High-arity coefficients and the
strict constant bound are checked as integer identities/inequalities; the
printed decimal constant is diagnostic.

The recursive checker checks nine explicitly listed construction trees,
thirty leaves and seventeen internal nodes, with N<=12. All Walsh/edge
counts are exact. Entropies and pointed invariants use rational logarithm
intervals from 24 atanh terms and a proved rational remainder. The separate
reviewer checker exhausts all 1,056 pointed positive-spectrum Boolean leaves
on two and three variables and certifies the generic score envelope and
C0=4 to C=23 leaf preparation by the same interval method.

The one-level checker uses eight exact spectra through N=12, with unequal
blocks and both parities. Its full-interaction, influence, coefficient and
chi-square assertions use integers or rational numbers; printed H/I values
are floating diagnostics. The support checker verifies 69,776 Boolean
completions (all functions through n=3 at every point with one/two dummy
bits, and all n=4 functions at one fixed point with one dummy bit), plus
four full-interaction examples through N=12. Its asymptotic table is
explicitly diagnostic only. Finite checks do not prove universal bounds;
the canonical manuscripts contain those proofs.

The general marked-set checker exhausts all 136 positive Boolean functions
on two and three coordinates and all their marked subsets of size at least
two: 31,704 marked instances. It also checks 298 rare-leaf instances and
15 internal nodes, q in {2,3,4,5,8}, maximum N=15, including adjacent leaf
marks, nonidentical signed leaves, and exact full-interaction witnesses.
Prime-factor log identities and rational 24-term atanh bounds certify the
assertions; no floating threshold is used for PASS.

The sharp-four supplement checks 32,927 rare marked sets: all containing the
exceptional point for n=2,3,4, and stated selected sets on n=5,6,8 through
q=256. Seven internal nodes have q in {2,3,4,5,8}, N<=15, including depth
two. Universal coefficient comparisons are checked by exact polynomial
identities, not by inferring all q from finitely many samples. This checker
imports its sibling general marked-set checker.

The approximation-barrier checker uses exact Walsh/edge/dual/Gram identities
for (n,m)=(2,3),(2,4),(3,3),(3,4), dimensions 6,8,9,12. It exhausts 26,973
coordinate subcubes for the first three cases. The cycle checker enumerates
all sixteen C4 states, exact energy and ground-layer degree, partition and
odd-denominator obstructions, and the stated Boolean period distinction.
All ranges and any diagnostic-only quantities are explicit in the sources.

Exact scientific revisions, reviewer scopes, complete proof-file hashes,
and the full-repository integrity result are in
[VERIFICATION.md](../VERIFICATION.md).


## Run the checks

From the public note directory
`notes/combinatorics/fourier-entropy-influence`, run:

```sh
python -B code/check_spectral_forest_arithmetic.py
python -B code/check_positive_spectral_forest_fei.py
python -B code/check_cycle_facet_arithmetic.py
python -B code/check_dyadic_feedback_forest.py
python -B code/check_integer_forest_logsobolev.py
python -B code/check_forest_selector_interpolation.py
python -B code/check_beyond_forest_bridge.py
```

The compiled scan can be run independently:

```sh
cc -O3 code/scan_ternary_integer_forests.c -lm -o /tmp/fei-ternary-scan
/tmp/fei-ternary-scan 3
```

The optional exhaustive four-variable scan is:

```sh
/tmp/fei-ternary-scan 4
```

Its parameter range is one through four. The four-variable run examines
$`3^{16}=43{,}046{,}721`$ ternary truth tables. The default when no argument
is supplied is four, so pass `3` explicitly for the smaller replay.

## What each program checks

| Program | Public proof and exact range | Numerical parts and limits |
| --- | --- | --- |
| [check_spectral_forest_arithmetic.py](check_spectral_forest_arithmetic.py) | [Forest arithmetic](../forest-arithmetic.md): explicit four-bit path core and two 12-input prefix/bent completions, all 4,096 truth values and integer Walsh coefficients; exact rational entropy and influence. | Does not search all forest spectra or prove the general completion theorem. |
| [check_positive_spectral_forest_fei.py](check_positive_spectral_forest_fei.py) | [Positive forests](../positive-forests.md): all 65,814 Boolean truth tables through four variables; 37,926 tree energies; four- and six-bit core parameters; actual hard-zero Boolean stars for $`k=3,4,5`$. | The tree-energy sample has fields in $`\{-1,0,1\}`$ and couplings in $`\{-1,1\}`$, all labelled trees through four vertices and paths on five and six. It does not replace the simultaneous induction. |
| [check_cycle_facet_arithmetic.py](check_cycle_facet_arithmetic.py) | [Cycles and cacti](../cycles-and-cacti.md): all 252 odd-edge cycle normal forms of lengths three through eight, 43,680 point checks; 1,574,912 Boolean modular tests at primes three and five, including 11,680 eligible exact lifts; the $`K_5`$-facet counterexample; 200 constructed cacti with seed 20261116; all 2,047 nonempty cutsets of the eleven-vertex path square. | The 200 cacti are generated controls, not an exhaustion of all cacti. The cut-polytope theorem remains a classical external input. |
| [check_dyadic_feedback_forest.py](check_dyadic_feedback_forest.py) | [Spectral conditioning](../spectral-conditioning.md): two exact 12-input cycle realizations; all 65,814 Boolean functions through four variables, 60,500 eligible cutsets and 223,944 integer sections; 6,654 ternary functions and 342 eligible forest sections at scales 1, 2, and 8; exact odd-factor counterexamples. | Its finite forest classifier includes coordinate-subcube support but does not exhaust general deterministic-edge quotients. Excluding those cases only reduces the test scope. |
| [check_integer_forest_logsobolev.py](check_integer_forest_logsobolev.py) | [Integer forests](../integer-forests.md): exact scalar certificates and all ternary functions on one, two, and three variables, with 4, 48, and 704 positive forest spectra respectively. | Entropy ratios and comparisons on 1,400 integer-factor tensors through seven bits and 500 integer product functions through six bits use floating point. They are diagnostics, not interval certificates or universal proofs. |
| [check_forest_selector_interpolation.py](check_forest_selector_interpolation.py) | [Interpolation](../interpolation.md): all fourteen Bernstein coefficients in rational arithmetic; certified logarithm enclosures for 16,660 eligible ordered branch pairs through three data bits; bent selectors for $`m=1,2,3`$; first-hit lists for $`m=1,2`$ and $`1\le k\le6`$; explicit balanced gate and exact composition recurrences. | Decimal entropy displays come from certified enclosures. The 257-input obstruction is evaluated by the proved recurrence, not by enumerating its truth table. |
| [check_beyond_forest_bridge.py](check_beyond_forest_bridge.py) | [Mixtures and obstructions](../mixtures-and-obstructions.md): all 65,814 Boolean functions through four variables, including 65,752 noncharacter minimum-layer checks; all sixteen majority-supported Boolean functions; exact tree projection; the four-bit core's eight-bit independent fair-completion lower bound. | Does not prove a universal mixture or denominator budget. The six-bit core is checked by the positive-forest program above. |
| [scan_ternary_integer_forests.c](scan_ternary_integer_forests.c) | [Integer forests](../integer-forests.md): exact Walsh transforms, positivity, multiplicative pairwise/forest recognition, counts, and largest odd Walsh part for all ternary functions on the requested dimension, at most four. | Printed entropy ratios and reported ratio maximizers are floating-point diagnostics. At four variables the author-run exact counts were 43,776 positive forests and largest odd part nine; independent replay was through three variables. |

## Interpreting a successful run

The universal inequalities are proved in the manuscripts. These programs
guard exact examples, formulas, integer divisibility, support handling,
certificate transcription, and finite classifications. They do not prove
FEI for an untested class and do not establish historical priority.

Some older checks retain weaker forest completion bounds of six or ten
fair bits. Those inequalities remain valid. The Boolean minimum-layer
refinement gives the stronger bounds eight and twelve; the bridge checker
verifies the former, and the latter follows from the six-bit parameters
and the displayed general proof.


## Positive bounded-treewidth continuation

From this directory, run:

```sh
python -B check_bounded_treewidth_integer_spectra.py
python -B check_connected_triangle_spectral_family.py
python -B check_forest_slack_continuation.py
```

These three files are byte-identical to scientific revision
`566b6a1a6ac3ff0b8ef1684d467b5ec904bcbe57`; all three were rerun here.
They use the standard library. The first verifies the nine integer scalar
certificates, the two strict constant comparisons, 65,814 Boolean functions,
6,654 ternary functions, and 300 exact gcd bag factorizations with seed
20261116. The eligible raw-entropy comparisons use integer exponentiation,
not floating logarithms.

The connected-family program checks the complete twelve-bit base function
and the exact core laws for one through four blocks, including their cubic
interactions, tree decomposition, feedback cut, entropy and influence.
Its optional `--full-two-block` argument requires NumPy and verifies every
signed Walsh coefficient of the actual 24-variable two-block function.
That optional run was performed by both the author and a nonauthor reviewer,
but was not repeated during public adaptation.

The zero-edge program checks 89,480 admissible physical sections, exact
energy stars, the integer star at N=16 and M=2, the seven-bit path, and the
six-bit Boolean two-star counterexample. The latter has 25 positive Fourier
atoms and exact half-integer sections on the second forbidden-edge cut.
These finite checks supplement the complete analytic proofs in
[bounded treewidth](../bounded-treewidth.md),
[connected triangles](../connected-triangles.md) and
[zero edges](../zero-edges.md); they are not extrapolated to prove a theorem.
