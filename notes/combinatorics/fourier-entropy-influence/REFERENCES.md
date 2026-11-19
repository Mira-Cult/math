# References and mathematical attribution

**Mira Cult · 16 November 2026**

The references below identify the external inputs and the closest
comparisons used in this public account. The scope of the literature
comparison is bounded; absence from this list is not a claim of novelty.
The local proofs and exact limitations are indexed in [CATALOGUE.md](CATALOGUE.md).

## Additional applicability audit for the marked-set theorem

[The approximation/certificate barrier proof](approximation-barriers.md)
checks Paraashar--Saurabh, *Fourier Entropy Bounds via Approximations*
([arXiv:2611.06451](https://arxiv.org/abs/2611.06451)), Theorems 3.1--3.2
and 4.1--4.5, against the exact hypotheses used here. The reviewed primary
PDF has SHA-256
`1dc89657a0b45c741df18eed86c8e4564f9ef2fc103d581d5af9b7a021bbc178`.

Pointwise approximation and multiscale mean-square approximation are different
hypotheses. The Gram result requires positive-semidefinite domination and
exact total squared mass. Orthogonal pieces satisfy a special case; the
natural signed point corrections do not. The affine indicator representation
results cannot be replaced by an ordinary-coordinate certificate assertion.
Our negative results concern ordinary coordinate subcubes and pointwise
approximate norm, and explicitly leave affine parity certificates and
mean-square approximations open. The inspected literature does not directly
supply the general marked-set closure from an ordinary child FEI bound;
this is a scoped applicability conclusion, not exhaustive publication
priority or noncontainment in every known class.


## Uniform-interaction continuation: source and applicability audit

The new class theorems are in
[directed factors](directed-factors.md),
[affine forests](affine-forests.md),
[recursive point modifications](point-modifications.md),
and [one-level point interference](one-point-products.md).
The [support reduction](positive-support.md) is an
exact same-constant equivalence, not an FEI proof. The following primary
sources were inspected again for applicable hypotheses and priority limits.

- **OWZ11**, [primary author PDF](https://www.cs.cmu.edu/~odonnell/papers/fei.pdf),
  Section 1.2 and Theorems 1--3. Tensorization and removal of an o(n)
  additive error are already established there. The d-part-symmetric
  bound is `12.04+log2 d`; applying it to the recursive construction's
  physical leaf blocks retains an unbounded part count. Read-once decision
  trees have the stated separate 4.88 bound.
- **OT13**, [primary author PDF](https://www.cs.cmu.edu/~odonnell/papers/fei-composition.pdf),
  Theorems 1--3 and FEI+ definition. A composition uses one Boolean output
  per disjoint physical child block and a biased corrected-entropy
  hypothesis for the outer gate. It does not permit an uncharged extra
  all-marked flag, nor does a uniform-input child FEI bound imply every
  needed biased outer bound.
- **WWW14:** Andrew Wan, John Wright and Chenggang Wu, *Decision trees,
  protocols, and the entropy-influence conjecture*,
  [primary author PDF](https://www.cs.cmu.edu/~jswright/papers/readk.pdf),
  Theorem 1.1 and Section 2. The bound `H<=9kI` uses k occurrences of each
  variable in the entire decision tree. It does not mean one read per path
  in an arbitrary branching program.
- **ShmaloThreshold26**, [arXiv:2610.16069v1 full HTML](https://arxiv.org/html/2610.16069v1),
  Theorems B--D, Sections 6--7 and Corollary 7.3. Arbitrary Boolean
  combinations of m regular functions retain `11.238+3.4log2 m`;
  the bounded-overlap theorem concerns unions/intersections. The uniform
  read-once formula theorem admits symmetric threshold and parity gates
  with arbitrary fan-ins and product biases. It does not automatically
  cover arbitrary symmetric gates or reused physical variables.
- **Carlet**, *Boolean Functions for Cryptography and Coding Theory*,
  [author monograph](https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf),
  Section 2.3, printed page 89. Odd truth-table weight implies nonzero
  Walsh transform. The completion proof repeats this elementary modulo-four
  calculation explicitly; novelty is not claimed for the congruence.

The recursive operation needs both a child's sign and its all-marked flag.
For four leaf activations, the two child signs are encoded by `a OR b`
and `c OR d`, while the root bit is their XOR further XOR `abcd`.
Inputs `(1,0,1,1)` and `(1,1,1,1)` have the same child signs and different
root signs. Thus direct one-output-per-child composition fails on the
construction tree. This does not prove absence of every alternative known
representation of the resulting function.

The explicit prefix/bent examples witnessing growing interaction size in
the directed and affine theorems already belong to the integer flat-packet
class. Their graphs alone are not evidence of a new FEI class. The new
mathematical content is the arity-free directed-load payment, the stronger
integer-tree partition sum and Boolean fair-subspace budget, and the
point-score invariant closing arbitrary-depth recursion. The special
one-level two-block family is already a read-once OR of rare events.
No exhaustive priority certification or noncontainment in every prior
class is asserted. The exact review scopes are recorded in [VERIFICATION.md](VERIFICATION.md).


## External proof inputs

- **[BM86]** Francisco Barahona and Ali Ridha Mahjoub, *On the cut polytope*,
  Mathematical Programming **36** (1986), 157–173.
  [DOI 10.1007/BF02592023](https://doi.org/10.1007/BF02592023);
  [author-hosted PDF](https://www.lamsade.dauphine.fr/~mahjoub/Papers/BM86.pdf).
  Theorems 3.3–3.4 and Corollary 3.10, especially printed pages 169–170,
  provide the edge/cycle description for graphs with no $`K_5`$ minor.
  The exact version used is stated in [cycles and cacti, Section 4](cycles-and-cacti.md#4-the-precise-cut-polytope-input).
  Its proof is an external classical dependency, not a theorem reproved
  by the finite cycle checks.
- **[Gross75]** Leonard Gross, *Logarithmic Sobolev Inequalities*,
  American Journal of Mathematics **97** (1975), 1061–1083.
  [DOI 10.2307/2373688](https://doi.org/10.2307/2373688).
  The cube inequality used here is
  $`\mathrm{Ent}(A^2)\le2\sum_i\mathbb E(D_iA)^2`$ with natural
  logarithms and half-difference derivatives. This normalization is stated
  in the introduction of [OWZ11], page 2, and in
  [O'Donnell's CMU problem set 4, problem 2](https://www.cs.cmu.edu/~odonnell/boolean-analysis/homework4.pdf).
- **[Pot26]** Vladimir N. Potapov, *On the Fourier Entropy-Influence
  Conjecture for Boolean Plateaued Functions*,
  [arXiv:2609.21563v1](https://arxiv.org/abs/2609.21563v1), 18 September 2026.
  Proposition 4 and Theorem 2 supply the support-degree argument and the
  determinant support-weight inequality used for the plateaued constant
  four. [Integer flat packets](integer-flat-packets.md) includes the full
  argument and states precisely its integer-valued extension. These
  underlying support arguments and the plateaued theorem are credited
  to this source rather than presented as new here.
- **[CarletMM]** Claude Carlet, *Boolean Functions for Cryptography and
  Error Correcting Codes*, Section 7.5.1, equations (59)–(60), printed
  page 119. [Author chapter PDF](https://www.math.univ-paris13.fr/~carlet/chap-fcts-Bool-corr.pdf);
  [expanded book](https://www.math.univ-paris13.fr/~carlet/book-fcts-Bool-vect-crypt-codes.pdf).
  The generalized Maiorana–McFarland construction and its Fourier fiber
  formula underlie the prefix-cylinder/bent completion. The latter is
  given explicitly in [forest arithmetic, Section 6](forest-arithmetic.md#6-every-powers-of-four-law-has-a-boolean-completion-with-independent-fair-spectral-bits).
  No novelty is claimed for the construction family or bent phases on
  affine fibers.

## FEI, composition, and selector comparisons

- **[FK96]** Ehud Friedgut and Gil Kalai, *Every monotone graph property
  has a sharp threshold*, Proceedings of the American Mathematical
  Society **124** (1996), 2993–3002.
  [DOI 10.1090/S0002-9939-96-03732-X](https://doi.org/10.1090/S0002-9939-96-03732-X).
  Historical origin of FEI, as attributed in [OWZ11].
- **[OWZ11]** Ryan O'Donnell, John Wright and Yuan Zhou, *The Fourier
  Entropy–Influence Conjecture for certain classes of Boolean functions*,
  ICALP 2011. [Author PDF](https://www.cs.cmu.edu/~odonnell/papers/fei.pdf).
  The introduction fixes the standard entropy and influence conventions;
  later sections treat symmetric functions and read-once decision trees.
- **[OT13]** Ryan O'Donnell and Li-Yang Tan, *A composition theorem for
  the Fourier Entropy-Influence conjecture*,
  [arXiv:1304.1347v1](https://arxiv.org/abs/1304.1347v1), 4 April 2013;
  [author PDF](https://www.cs.cmu.edu/~odonnell/papers/fei-composition.pdf).
  Theorem 1 uses disjoint physical input blocks and the appropriate
  biased corrected entropy for the outer gate. The bounded-arity
  read-once conclusion does not automatically apply to shared data or
  to non-Boolean partial Fourier sections. Balanced disjoint composition
  identities used in the explicit gate obstruction are an elementary
  special case of this framework.
- **[Shmalo26]** Yitzchak Shmalo, *Fourier entropy of threshold functions
  and their compositions*,
  [arXiv:2610.16069v1](https://arxiv.org/abs/2610.16069v1), 12 October 2026;
  [HTML](https://arxiv.org/html/2610.16069v1).
  Proposition 8.6 gives the exact shared-data selector identity and
  $`H(F)\le2k+\mathbb E H(g_z)`$. Corollary 8.7 gives FEI bounds from
  neighboring-branch orthogonality or a lower bound on selector influence.
  Those identities already give a coarser dimension-independent bound
  for the first-hit lists considered here when combined with forest leaf
  estimates. The new argument preserves constant four through a half-bit
  influence-corrected query defect; it does not claim the first constant
  FEI estimate for every displayed selector example.
- **[GS14]** Sugata Gangopadhyay and Pantelimon Stănică, *The Fourier
  Entropy-Influence conjecture holds for a log-density 1 class of
  cryptographic Boolean functions*,
  [Cryptology ePrint 2014/054](https://eprint.iacr.org/2014/054);
  [PDF](https://eprint.iacr.org/2014/054.pdf).
  Section 4.2, Theorem 8 treats concatenation under disjoint Fourier
  spectra. The relevant exact hypothesis was checked through primary
  indexed PDF text; direct full-PDF retrieval was unavailable in the
  recorded comparison. The interpolation result here permits overlapping
  spectra. The paper also discusses plateaued functions and earlier
  cryptographic FEI classes.
- **[Hod17]** Rani Hod, *Improved Lower Bounds for the Fourier
  Entropy/Influence Conjecture via Lexicographic Functions*,
  [arXiv:1711.00762v1](https://arxiv.org/abs/1711.00762v1), 2 November 2017.
  Its three explicit asymptotic constructions include a lower bound
  $`C>6.454784`$, even for monotone functions. This shows why a universal
  extension cannot retain constant four. No claim is made that this is
  the most recent or best lower bound.

## Scope of the comparison

The proofs here do not equate fractional certificates with integer
packets, affine partitions, or unambiguous selectors. Nor is a positive
probability law assumed Boolean-realizable from its marginals. The
classical composition and construction methods cover some explicit
examples in this collection; a cyclic dependency graph alone is not
evidence that an example lies outside all previously known FEI classes.

The external inputs above are mathematical dependencies or specific
comparisons, not a complete literature survey. [VERIFICATION.md](VERIFICATION.md)
separates primary-source checking, mathematical review, and finite replay.


## Bounded-treewidth continuation

The [bounded-treewidth theorem](bounded-treewidth.md) proves its integer
gcd factorization and entropy tensorization directly. Its nine local
scalar certificates are exact integer comparisons. The statement does not
rely on the cut-polytope theorem, odd-prime exclusion or an AA conversion.
The earlier Gross-based proof remains a distinct stronger-constant method
for integer forests.

The primary O'Donnell–Tan composition PDF and O'Donnell–Wright–Zhou PDF
were re-opened for the comparison of hypotheses and normalizations.
The connected triangle construction uses the credited generalized
Maiorana–McFarland prefix/bent completion; its particular functions are
not claimed as previously unproved FEI examples. The zero-edge note
preserves the earlier constant-four depth-two product case and states
its extension to nonproduct forest sections separately.

Focused primary-source searches for Fourier entropy with treewidth,
graphical integer spectra and spectral Markov laws did not locate this
bounded-treewidth theorem. This is a limited literature check, not a
global historical priority certification. The standing universal FEI
question, its known lower-bound examples and the sources above retain
their stated scope.


### Earlier depth-two product-leaf bound

Mira Cult, *Half-integer defect repair and constant four at spectral depth
two*, Theorem 2 in Section 2, research source
[half_integer_product_repair.md at 566b6a1a6ac3ff0b8ef1684d467b5ec904bcbe57](https://github.com/Mira-Cult/math-wip/blob/566b6a1a6ac3ff0b8ef1684d467b5ec904bcbe57/problems/0298-fourier-entropy-influence-conjecture/manuscripts/half_integer_product_repair.md#2-constant-four-for-an-adaptive-spectral-tree-of-depth-two).
This is a historical comparison: the earlier theorem already covers
product conditional leaves at spectral depth two. The public
[forbidden-pair proof](zero-edges.md) is complete here and does not depend
on access to that research source; its additional hypothesis permits
nonproduct positive forest sections and its conclusion uses influence
outside the cut.
