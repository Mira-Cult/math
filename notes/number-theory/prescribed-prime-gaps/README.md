# Prescribed prime gaps: coverings and signed endpoint estimates

**Mira Cult · 16 November 2026**

For every sufficiently large even integer $`g`$, there is a congruence class
whose two endpoints differ by exactly $`g`$, remain coprime to the covering
modulus, and have every intermediate integer forced composite. The modulus is
subexponential in $`g`$:

```math
\log M=(8+o(1))g\frac{\log\log\log g}{\log\log g}=o(g).
```

The proof preserves an arbitrary even difference, including differences with
large prime factors. It uses only the prime number theorem, Mertens' product
theorem, Brun–Titchmarsh and elementary congruence arguments.

**The endpoint-primality step remains open.** This note does not prove that
every even integer occurs as a consecutive-prime gap, or a new infinite family
of specified prime gaps. Its uniform theorem concerns complete coverings and
consecutive reduced residues. No historical priority is claimed.

The analytic continuation now proves two transfer results: a single family
of twisted squares controls the whole cofactor range with its moving cutoffs,
and primitive-root counts hold for arbitrary moduli with the prescribed-gap
residue densities. It also identifies a genuine failure of absolute marking
removal on the actual primes. The needed signed base estimate and the signed
contribution of the unmarked sector remain open.

## Results and proofs

| Result | Exact scope | Canonical proof |
|---|---|---|
| Prescribed endpoint cover | For all sufficiently large even $`g`$, a complete interior cover modulo $`M=\prod_{p\le y}p`$, with $`y=8(g+1)\log_3(g+1)/\log_2(g+1)`$, preserving both endpoints | [Theorem C-SUB](cover.md#the-covering-theorem) |
| Uniform primorial gap prefix | For every fixed $`c\lt 1/8`$, all even $`g\le c p\log_2p/\log_3p`$ occur between consecutive integers coprime to $`p\#`$, for every sufficiently large prime $`p`$ | [Corollary C-RESIDUES](cover.md#a-uniform-interval-of-gaps-between-reduced-residues) |
| Erdős's existence question | The smallest missing even gap tends to infinity exactly when every even prime gap occurs at least once | [Proposition R1](first-occurrence.md) |
| Erdős's stronger rate | Assuming every gap occurs, $`r(x)/\log x\to\infty`$ is equivalent to a subexponential first-occurrence bound, in prime index or prime location | [Proposition R2](first-occurrence.md) |
| Finite prime-gap bridge | Exact occurrences of every even gap through 180, with prime endpoints and proper divisors for every interior number | [Certificates](evidence/gaps-through-180.json) and [verifier](code/gap_certificates.py) |
| Signed endpoint identity | Classical calibrated positive main term plus an exact signed remainder; a stated one-sided remainder bound would force endpoint primality | [Theorem 1 and Corollary 2](signed-endpoint-transfer.md) |
| Cofactor and cutoff transfer | An unconditional inequality transfers a phase-uniform base-energy bound to all cofactors and maximal moving intervals; that base bound is still unproved | [Theorem D3 and corollaries](cofactor-dispersion.md) |
| Arbitrary-modulus root counts | Uniform determinant-one completion counts and exact fixed-gap unit-ratio/projective-line densities | [Theorem RC1 and Corollary RC2](root-counting-moduli.md) |
| Fixed-gap operator transfer | Exact residue-component and intermediate-primitivity adapters; the marked estimate is conditional on listed external analytic contracts | [Conditional interface theorem](fixed-gap-operator-transfer.md) |
| Rough-endpoint localization | The full small-divisor main term lies on endpoints avoiding the auxiliary band; absolute marking removal has an oversized unsigned budget | [Theorems 4 and 6](rough-endpoint-marking.md) |
| Protected-class parity | A prime-free comparison retains the relevant divisor statistics, including a polylogarithmic growing-modulus range; a Chen repair needs a localized sign estimate | [ER1–ER4 and ER3u](endpoint-repair.md) |

The unconditional results have complete proofs with their classical analytic
inputs explicitly cited. The fixed-gap operator transfer has a separate
conditional proof from the listed external analytic contracts; those
contracts have not been independently certified here.
The asymptotic covering threshold is not numerical.
The first-occurrence note separates a location bound from an index bound and
states the unproved two-form input that would connect the cover to either
Erdős question.

## What the signed method gains

For a protected class $`a\pmod Q`$, classical distribution calibrates

```math
\sum_{\substack{X\lt n\le2X\\n\equiv a\pmod Q}}
 \vartheta(n)\Lambda(n+g)
=\kappa(Q,g)X+R_D(X)+o(X).
```

The hard term is a signed sum over $`cd=n+g`$. Grouping its marked squares
by $`k=ch`$ turns the sum over $`c`$ into a divisor weight. A proved fourth-moment
envelope pays that weight without a worst-case divisor loss. Half-integer
sine inversion handles the actual lower divisor cutoff and product window.
This removes the need for a separate relative $`1/c`$ estimate at every
cofactor. It transfers cancellation once available; it does not create it.

The auxiliary marks leave a sparse sector that must be retained. If
$`V\asymp(\log X)^{\alpha-\beta}`$ is the probability of avoiding their
full prime band, the small-divisor main term still lies entirely on that
sector. For divisor markers vanishing there, the unsigned removal budget is
at least a constant times $`XV^2(\log X)^2`$. This rules out the stated
absolute-error method. It leaves signed cancellation as a possible route.

## Why the cover is smaller

Translate the protected offsets to $`1,g+1`$. Most medium-prime residue classes
can then be set to zero. Omit medium primes dividing the right endpoint, and
bound the survivors arising from these exceptional factors uniformly by a
Rankin sum. Choose nonzero classes at the small primes; surviving large prime
cofactors can then be counted by Brun–Titchmarsh in reduced residue classes.
The remaining reserve primes remove every interior survivor while avoiding
both endpoints. The cleanup budget gives the displayed modulus.

This is a quantitative variant of established Erdős–Rankin and protected-tuple
constructions. [The comparison](cover.md#comparison-for-this-corollary)
distinguishes it from Holt–Rudd's fixed-gap primorial theorem and Ziller's
explicit $`N_{\min}(k)\ge2k`$ bound. The new growing-range bound exceeds that
identified baseline; a complete external priority assessment is still open.

## Reproduce the finite certificates

From this directory, with Python 3.12 and no third-party packages:

```sh
python code/gap_certificates.py verify evidence/gaps-through-180.json
python -O code/gap_certificates.py verify evidence/gaps-through-180.json
python code/cofactor_dispersion_checks.py
python -O code/cofactor_dispersion_checks.py
python code/root_counting_checks.py
python -O code/root_counting_checks.py
python code/rough_endpoint_checks.py
python -O code/rough_endpoint_checks.py
```

Both modes verify 90 gaps, 180 prime endpoints by exact trial division, and
8,100 proper interior divisors. The largest endpoint is 83,751,287. Recorded
generator indices are metadata, not certified minimal first-occurrence indices.
The finite certificate does not establish any infinite family.

The continuation scripts check 43,568 cofactor/cutoff identities, 25,232
modular root identities and densities, and 61,741 marking/convolution
identities. The modular check independently enumerates 243,726
determinant-one matrices. These are exact finite checks; the asymptotic
theorems are supported by their conventional proofs and scoped reviews.

## What remains to prove

For a cover $`a\pmod M`$, prove that the two particular forms $`Mt+a`$ and
$`Mt+a+g`$ are simultaneously prime. Admissibility is established; simultaneous
primality is not. A polynomial bound in $`M`$ for the first such pair would,
combined with the subexponential modulus and a finite bridge, imply the
stronger Erdős rate. That quantitative two-form assertion is unproved and is
not ordinary Linnik's theorem or a consequence supplied by qualitative Dickson.

For the signed approach, the precise remaining tasks are:

1. Prove the phase-uniform base-energy estimate D11 for the actual fixed-gap,
   protected-progression coefficients, including the complete operator and
   major-arc argument.
2. Control the signed unmarked contribution, or replace it by a proved
   centered transfer, off-endpoint weighted correlation, or Chen-support
   sign estimate. The displayed absolute-removal architecture is ruled out.
3. If the covering data grow, pay all errors relative to $`\kappa(Q,g)X`$.
   A fixed-gap asymptotic has no automatic uniform first-occurrence rate.

## Review and sources

[Verification](VERIFICATION.md) records the exact source revision, independent
model-review scope and executable checks. This is a conventional mathematical
research note, not a formalization or externally refereed paper.

The motivating questions are [Erdős problem 853](https://www.erdosproblems.com/853),
with its [official history](https://www.erdosproblems.com/history/853). Primary
covering and sieve references appear beside their use in the full proof.
