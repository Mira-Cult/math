# References

These are the primary sources used by the proof. Versions and theorem locators
are recorded so that the imported hypotheses can be checked against the
arguments in this note. The additional consequences needed here are proved in
the linked components, rather than attributed to a stronger published theorem.

## Classical estimates for the explicit bound

The four explicit supplement files use the following three sources. The
additional signed smoothing estimate E2 and the specialized progression
interfaces S40 are derived in [classical-primes.md](classical-primes.md),
not attributed verbatim to stronger published statements.

### Rosser–Schoenfeld: ordinary primes and the exact pool

J. Barkley Rosser and Lowell Schoenfeld, *Approximate formulas for some
functions of prime numbers*, Illinois Journal of Mathematics 6 (1962),
64–94, DOI [10.1215/ijm/1255631807](https://doi.org/10.1215/ijm/1255631807).
Source: [scan of the original paper](https://denisevellachemla.eu/Rosser-Schoenfeld-1962.pdf).

**Locators:** printed page 69, Theorem 1 and Corollary 1, equations (3.2),
(3.5) and (3.6).

**Use:** explicit upper and lower bounds for $`\pi(x)`$ give the index bound,
mean bounds for the first $`n^2`$ odd primes, and the all-scale consecutive-prime
matching E1. The prime 2 is explicitly excluded in the pool-total identity.

### Bennett–Martin–O'Bryant–Rechnitzer: progression estimates

Michael A. Bennett, Greg Martin, Kevin O'Bryant and Andrew Rechnitzer,
*Explicit bounds for primes in arithmetic progressions*, Illinois Journal
of Mathematics 62 (2018), 427–532. The version used is the
[author-hosted journal PDF](https://personal.math.ubc.ca/~gerg/papers/downloads/EBPAP.pdf).

**Locators:** equations (2.2), (2.4)–(2.6) and the explanation on printed
page 439; Proposition 1.11; Definition 6.1; Proposition 6.2 and its proof;
Lemma 6.7; equations (6.14)–(6.16); Lemmas 6.8–6.11; Proposition 6.16
and its hypotheses (6.23).

**Use:** the real-zero bound, zero-sum bounds and proper-prime-power estimate
enter E2. The strong interface S40-S evaluates Proposition 6.16 at
$`Z=8`$, $`\kappa_1=1`$, $`\kappa_2=\kappa_3=2^{20}`$.
The weak interface S40-W retains the sign and size of a possible exceptional
zero. Both interfaces hold uniformly for the stated growing modulus ranges.
These imported estimates include their published computational inputs; the
note does not re-certify those computations.

### McCurley: the primitive explicit formula

Kevin S. McCurley, *Explicit estimates for the error term in the prime number
theorem for arithmetic progressions*, Mathematics of Computation 42 (1984),
265–285, DOI
[10.1090/S0025-5718-1984-0726004-6](https://doi.org/10.1090/S0025-5718-1984-0726004-6).
Source: [publisher PDF](https://www.ams.org/mcom/1984-42-165/S0025-5718-1984-0726004-6/S0025-5718-1984-0726004-6.pdf).

**Locators:** Section 3, especially the zero-set convention on printed page
271; Lemmas 3.1–3.2; equations (3.4)–(3.5) and (3.10); and the
primitive-character identity immediately before (3.16).

**Use:** the characterwise explicit formula, after two positive averages,
provides the primitive spectral and nonspectral terms in E2. Induced
characters are handled by explicitly subtracting the missing Euler-factor
prime-power sums. The access and review limitation for the original PDF is
recorded in [Provenance](PROVENANCE.md#explicit-cutoff-adaptation-and-review-boundary).

## Sources for the original qualitative proof

The following references belong to the retained original qualitative argument.
Its threshold was not evaluated there.

## Bounded gaps and quantitative seed supply

James Maynard, *Small gaps between primes*, Annals of Mathematics 181 (2015),
383–413, DOI [10.4007/annals.2015.181.1.7](https://doi.org/10.4007/annals.2015.181.1.7).
The proof version used is
[arXiv:1311.4600v3, 28 October 2019](https://arxiv.org/pdf/1311.4600v3).

**Locators:** Propositions 4.1 and 4.3, the proof of Proposition 4.2,
equation (5.9), and the admissible 105-tuple of diameter 600 in footnote 2
on printed page 6.

**Use:** [Controller Lemma S](controller.md#s-a-supply-of-common-bounded-gaps-for-every-sufficiently-large-pool)
derives a quantitative supply of disjoint common-gap pairs at every
sufficiently large scale. It divides a positive weighted sieve surplus by a
bound for the largest weight, then applies a matching and finite pigeonhole
argument. The selected even gap $`g\le600`$ and reduced residue class may vary
with the scale. Merely knowing that bounded gaps occur infinitely often would
not supply the required conclusion.

## Almost-equal ternary primes

Kaisa Matomäki, James Maynard and Xuancheng Shao, *Vinogradov's theorem with
almost equal summands*, Proceedings of the London Mathematical Society (3)
115 (2017), 323–347, DOI
[10.1112/plms.12040](https://doi.org/10.1112/plms.12040).
The proof version used is
[arXiv:1610.02017v2, 13 March 2017](https://arxiv.org/pdf/1610.02017v2).

**Locators:** Theorem 2.1 and its proof on printed pages 5–6, including the
restriction-estimate footnote; Proposition 3.1; and the verification of the
analytic hypotheses in Section 5.

**Use:** [A1](prime-targets.md#a1-almost-equal-ternary-primes-in-prescribed-fixed-classes)
derives the prescribed-class version for a fixed even modulus, including
prime powers, by replacing $`W`$ with $`\mathrm{lcm}(q,W)`$. It accounts
for the Fourier error, lower density, restriction norm, lifted residues and
exact convolution target. The published headline theorem does not prescribe
individual residue classes; that extension is proved here. [A3](prime-targets.md#a3-prime-vectors-with-exact-total-uniformly-in-their-length)
then obtains a threshold independent of vector length by a deterministic
balancing argument. The analytic convolution always has three variables.

## Prime number theorem in fixed progressions

Dimitris Koukoulopoulos, *Pretentious multiplicative functions and the prime
number theorem for arithmetic progressions*, Compositio Mathematica 149
(2013), 1129–1149, DOI
[10.1112/S0010437X12000802](https://doi.org/10.1112/S0010437X12000802).
Source: [author manuscript dated 13 March 2013](https://dms.umontreal.ca/~koukoulo/documents/publications/pnt.pdf),
corresponding to [arXiv:1203.0596v3](https://arxiv.org/abs/1203.0596v3).

**Locator:** Theorem 1.1, printed page 2, specialized to fixed moduli.

**Use:** The controller needs positive-density prime supplies in each
specified reduced class in intervals of fixed positive relative length.
Ordinary partial summation gives the counting form. This fixed-progression application uses only finitely many moduli, bounded
by 600, and extracts no numerical threshold from the estimate.

## Order-three example

Dmitry Kamenetsky, [“Prime sums in a 3x3 grid”](https://puzzling.stackexchange.com/questions/114974/prime-sums-in-a-3x3-grid),
Puzzling Stack Exchange, question dated 19 February 2022; the answer by
Daniel Mathias on the same date gives the square reproduced in the
[main note](README.md#a-small-example).

This is a prior exact-pool example, not an input to the eventual-existence
proof. Its entries and all eight line sums can be checked directly. No
novelty assertion is made for either the example or the theorem in this note.

