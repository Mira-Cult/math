# Catalogue of results and their scopes

**Mira Cult · 16 November 2026**

This is the authoritative catalogue for the public FEI notes.
“Proved” below means a complete conventional argument with the stated
classical imports. It does not mean formal verification, journal acceptance,
or an exhaustive novelty certification. The exact model-review and
computation scopes are in [VERIFICATION.md](VERIFICATION.md).

All entropy is in bits. The [overview](README.md#the-question-and-conventions)
fixes the common Fourier and influence conventions. “Positive pairwise”
always means a full-support law with unary and two-coordinate potentials;
a general bag potential is not implicitly allowed.

## Entropy–influence theorems

| Result | Exact scope and conclusion | Canonical proof |
| --- | --- | --- |
| Sharp marked-set rare-point closure | For every fixed $`q\ge2`$, rare-point leaves of dimension at least two carry $`q`$ distinct marks including their exceptional point. Every node has $`m\ge2+\lceil\log_2q\rceil`$ disjoint children and flips the concatenated marks, distinct in each projection. Every finite construction has positive spectrum and $`H\le4I`$. One constant for all $`q`$; four is optimal for every fixed $`q`$. | [Sharp rare leaves, Theorem](marked-rare-leaves.md) |
| General marked-set closure | The same operation for a positive Boolean leaf class of dimension at least two with $`H\le C_0I`$ gives $`H\le[(5/4)C_0+7]I`$, independently of $`q`$, depth and arity. The same $`q`$ is used within a construction. Leaves with constants 4, $`C_2\lt14`$, and $`C_{\rm aff}`$ give 12, below 24.5, and below 28 respectively. | [Marked-set closure, Theorem 1](marked-set-closure.md) |
| Directed positive integer factors | Actual magnitudes $`2^n\lvert\widehat h\rvert=c\prod_\alpha u_\alpha`$, $`c\ge1`$, positive integer factors, at most one outgoing decrease per factor/state: $`H_{\rm raw}(h)\le4I(h)-2\lVert h\rVert_2^2\log_2c`$. No arity or overlap bound. | [Directed factors, Theorem 1](directed-factors.md) |
| Paid one-atom core | A positive Boolean spectrum becomes the preceding core after reducing one coefficient: $`H\le(4+1/\ln2)I`$; if the retained scalar is at least $`\sqrt e`$, $`H\le4I`$. The inverse core need not be integer-valued. | [One-atom repair](directed-factors.md) |
| Affine positive forests | Every injective affine image of a positive Boolean forest spectrum has $`H\le[4+4/\log_2(5/4)]I`$, with one constant below seventeen. Affine-subspace support is allowed exactly as stated. | [Affine forests, Theorem A](affine-forests.md) |
| Recursive rare-point modifications | Leaves are rare-point phases on at least two bits. Each internal node has at least two disjoint children, multiplies them and changes the marked truth value. Every finite construction satisfies $`H\le9I/2`$, independently of depth and arity. | [Point modifications, Theorem 1](point-modifications.md) |
| General positive-leaf closure | Any positive Boolean leaf class, each leaf dimension at least two, with a proved bound $`H\le C_0I`$ has the same recursive closure bound $`H\le[(3/2)C_0+17]I`$. Constant-four leaves give 23; width-two leaves give a constant below 38. | [Point modifications, Theorem 4](point-modifications.md) |
| One-level marked product | Arbitrarily many unequal rare-point blocks of size at least two, with the specified point flip: $`H\le4I`$, sharp for the class. Necessary direct factor arity is the full dimension and the positive interaction graph is complete. | [One-point products](one-point-products.md) |
| Positive width-two spectra | Integer-valued $`h`$ with a positive Fourier law on a graph of treewidth at most two, allowing genuine triangle potentials: $`H_{\rm raw}(h)\le C_2I(h)`$, $`C_2=2(2+\log_2 23)/\log_2(23/12)<14`$. Boolean FEI follows. | [Bounded treewidth, Theorem 1](bounded-treewidth.md) |
| Every fixed spectral width | Under the positive integer-function hypothesis, treewidth $`w`$ gives an explicit $`C(w)`$ independent of dimension, degree and value range. The constant grows with $`w`$. | [Bounded treewidth, Theorem 2](bounded-treewidth.md) |
| Forbidden-pair forest sections | Boolean forest law omitting a two-bit pattern, with positive forest sections after the stated quotients: $`H\le4\sum_{k\notin\{i,j\}}\mathrm{Inf}_k`$. Allows nonproduct forest pieces beyond the prior product-leaf special case. | [Zero edges, forbidden-pair corollary](zero-edges.md) |
| Positive Boolean forests | Full-support Boolean Fourier law factorizing over a forest: $`H\le4I`$. Zero-dimensional case handled separately. | [Positive forests, Theorem 5](positive-forests.md#6-the-unconditional-full-support-boolean-forest-fei-theorem) |
| Boolean forest deficit | For a nonconstant positive Boolean forest, $`H\le4I-2-2c`$, where $`c`$ counts nonconstant energy components after deleting zero interactions. | [Boolean minimum layer, Corollary 2](mixtures-and-obstructions.md#1-boolean-parity-strengthens-the-minimum-layer-bound) |
| Deterministic support extension | Remove fixed spectral bits and contract equality/complement edges. If the quotient is a positive forest, $`H\le4I`$. Three-state edges excluded. | [Deterministic contractions, Proposition 1](deterministic-contractions.md#1-all-deterministic-spectral-edges-can-be-contracted) |
| Common feedback vertex | Positive pairwise Boolean spectrum on $`G`$, with $`G-r`$ a forest: $`H\le4\sum_{i\ne r}\mathrm{Inf}_i`$. Arbitrarily many cycles may pass through $`r`$. | [Cycles, Corollary 2](cycles-and-cacti.md#1-main-statements) |
| Positive cacti | Positive pairwise Boolean spectrum on any cactus: $`H\le4I`$. When its minimal graph has a cycle, a constructed cutset $`K`$ gives $`H\le4I_{K^c}-2`$. No bound on cycle count. | [Cactus theorem and payment](cycles-and-cacti.md#6-paying-for-unboundedly-many-cactus-cycles) |
| Paid feedback sets | Positive pairwise Boolean spectrum of treewidth at most two; a feedback set $`K`$ of size $`k\ge1`$ leaves $`b`$ components containing genuine edges: $`H\le4I_{K^c}+2(k-1-b)`$. | [General component payment](cycles-and-cacti.md#6-paying-for-unboundedly-many-cactus-cycles) |
| Dyadic integer forests | Integer-valued $`h`$, positive forest spectrum, every nonzero Fourier magnitude an integer power of two: $`H_*\le4I-2c\lVert h\rVert_2^2`$. Deterministic quotients retain the bound without the stated refinement. | [Spectral conditioning, Theorem 1](spectral-conditioning.md#2-integer-forest-packets-with-unrestricted-amplitude-spread) |
| Dyadic spectral conditioning | Boolean power-of-two amplitudes and forest sections after $`k\ge1`$ spectral cuts: $`H\le4I_{K^c}+2k-2`$. Adaptive sections pay their actual mean denominator exponent. | [Fixed and adaptive conditioning](spectral-conditioning.md#3-a-spectral-cutset-theorem) |
| Arbitrary integer forests | Integer-valued $`h`$ with positive forest spectrum: $`H_{\rm raw}\le C_F I`$, $`C_F=6/\log_2(16/9)<8`$. No odd-prime or amplitude-spread hypothesis. | [Integer forests, Theorem 1](integer-forests.md#1-results-and-normalization) |
| Bounded spectral conditioning | Boolean spectrum partitioned into subcubes of codimension at most $`k\ge2`$, each positive-mass cell having a positive forest conditional law: $`H\le[32+1/\ln2+(2+8\ln2)(k-1)]I`$. Cellwise deterministic quotients allowed. | [Integer forests, Theorem 3 and proof](integer-forests.md#7-proof-of-the-general-conditioning-theorem) |
| Physical restriction trees | Arbitrary Boolean leaves: $`H-4I\le\mathbb E(H_L-4I_L)+\mathbb E D/2`$. Forest leaves give $`H\le4I+\mathbb E D/2-2P`$, with $`P`$ their nonconstant probability. | [Interpolation, Theorem 1](interpolation.md#1-the-interpolation-theorem) |
| Shared-data forest lists | First-hit lists with fresh uniform controls and nonconstant admissible forest payloads on the same data cube: $`H\le4I-1-2^{-k}`$ for $`k\ge1`$. | [Interpolation, Corollary 3](interpolation.md#1-the-interpolation-theorem) |
| Flat or bounded-spread integer packets | Boolean sum of integer-valued packets with disjoint Fourier supports: $`H\le4I`$ for flat packets, $`H\le4R^2I`$ if every packet's amplitude ratio is at most $`R`$. | [Integer flat packets, Theorems 1–3](integer-flat-packets.md) |

The positive-cactus and common-feedback-vertex conclusions also extend to
deterministic quotients when the quotient has the required positive graph.
The arbitrary-integer conditioning bound is weaker on positive pairwise
graphs with one feedback vertex, where the arithmetic theorem gives constant
four; it applies more generally to conditional forest sections without a
pairwise parent law.

## Structural estimates and exact obstructions

| Result | What is proved | What is not inferred |
| --- | --- | --- |
| [Uniform marked-set invariant](marked-set-closure.md) | Exact entropy/influence identities retain signed Fourier pair terms and internal marked edges. Product orthogonality and an integer-amplitude gap preserve the stated two-score margin uniformly in $`q`$. Rare-point leaf cancellation gives sharp constant four. | No uncharged collision of projected marks, overlap of physical blocks, changing $`q`$ within a tree, or arbitrary-leaf FEI assertion. |
| [Approximation and ordinary-certificate barriers](approximation-barriers.md) | Positive two-mark functions with $`I=2n`$ have ordinary nonnegative coordinate-subcube representation cost and log pointwise approximate spectral norm of order $`2^n`$. The natural tight-Gram correction fails, and its orthogonal repair remains costly. | Does not exclude affine parity certificates, multiscale mean-square approximations or every alternative decomposition. These functions satisfy $`H\le4I`$. |
| [Four-cycle partition obstruction](cyclic-obstruction.md) | An integer C4 energy has ground-layer parameter $`\kappa=2`$ and $`Z=40\lt2\cdot5^2`$. Its law has an odd denominator and is not Boolean-realizable, even after independent fair completion. | Refutes the unrestricted cyclic extension of the tree lemma, not a Boolean-sensitive extension or FEI. |
| [Tree partition and fair rank](affine-forests.md) | Nonconstant connected integer tree energies satisfy $`Z\ge2\,5^\kappa`$, with the two stated field comparisons. Boolean forest laws satisfy $`d\le[2+2/\log_2(5/4)]q`$ for their independent fair dimension. | No such partition bound is asserted on arbitrary cyclic energies, and no fair direction is forced in every positive Boolean law. |
| [Signed point invariant](point-modifications.md) | Exact entropy and influence changes; a score correction at most six at product nodes; a preserved margin for arbitrary recursive depth. Every positive Boolean function has the stated universal pointed-score envelope. | No free iteration of arbitrary point flips or uncharged overlap of physical blocks. |
| [Positive-support completion](positive-support.md) | Unrestricted FEI and FEI for all positive Boolean spectra have exactly the same optimal constant. Fixed near-balance with an $`o(n)`$ allowance also suffices. | An equivalence does not prove either bound, and the completion need not preserve any special factorization. |
| [Stronger absorption barrier](positive-support.md) | The fixed-$`\eta<1`$ absorption invariant fails even with mean and largest atom tending to zero, after removing the empty atom, and on connected complete-interaction Boolean spectra. | These examples satisfy constant-four FEI and do not disprove a different entropy payment. |
| [Integer gauge obstruction](directed-factors.md) | Every bounded-decrease factorization of the rare-point Walsh tensor has the displayed quadratic lower bound on log denominator. A two-block product requires at least $`2m`$ distinct atom reductions. | Refutes those uniform representation/one-atom conversions, not FEI or a paid blockwise repair. |
| [Integer bag factorization](bounded-treewidth.md) | Every positive integer graphical tensor of width $`w`$ has positive integer factors on bags of size at most $`w+1`$, by exact gcd elimination. | No bounded-arity representation for arbitrary Walsh tensors. |
| [Paid local entropy](bounded-treewidth.md) | Positive integer factors of arity at most three give $`D_2(p\Vert U)\le(15/16)L+2J`$, on any factor graph. Nine exact integer certificates close the local inequality. | Does not extend unchanged to integer hard-zero forest laws. |
| [Connected triangle family](connected-triangles.md) | Actual Boolean functions on $`12m`$ bits, positive spectra, genuine triple terms for $`m\ge2`$, and feedback vertex number $`m-1`$. | Class strictness is not a claim of first FEI bounds for the constructed functions. |
| [Hard-zero absorption barrier](zero-edges.md) | Integer three-state stars refute every uniform $`D_2\le\eta L+CJ`$ with $`\eta<1`$, while satisfying raw FEI. | Not a Boolean FEI counterexample; does not disprove a different norm-sensitive argument. |
| [Noniterable forbidden cuts](zero-edges.md) | A six-bit Boolean product of two genuine hard-zero stars yields an integer first packet and half-integer second sections. | Does not refute paid or differently organized decompositions. |
| [Forest odd-prime exclusion](forest-arithmetic.md#4-arithmetic-rigidity-of-boolean-spectral-forests) | Every nonzero Walsh magnitude of a Boolean forest spectrum is a power of two, including hard-zero laws. | No entropy bound for all hard-zero forests. |
| [Cycle-facet arithmetic](cycles-and-cacti.md#5-proof-of-arithmetic-rigidity) | A positive pairwise Boolean law on $`G`$ has power-of-two Walsh magnitudes when the suspension $`G^+`$ has no $`K_5`$ minor; in particular for pairwise treewidth at most two. | This arithmetic proof does not give constant four for all width two; it excludes triangle potentials. The separate entropy theorem above allows them. |
| [Boolean minimum layer](mixtures-and-obstructions.md#1-boolean-parity-strengthens-the-minimum-layer-bound) | For a noncharacter, $`\deg_{\mathbb F_2}\mathbf1[v_2(W)=m]\le m-1`$. The four-bit path core requires eight independent fair completion bits, and eight suffice. | No optimality claim for arbitrary correlated completions or for the six-bit core. |
| [Local integrality defect](integer-forests.md#32-a-paid-local-integrality-defect-on-arbitrary-graphs) | If $`K\lvert W_f\rvert`$ factors into positive integer unary/edge factors, then $`H(f)\le C_FI(f)+2\log_2K`$. | No universal influence bound on the least such $`K`$. |
| [Majority mixture obstruction](mixtures-and-obstructions.md#2-a-boolean-law-for-which-every-forest-mixture-is-a-point-mass-mixture) | Every mixture of Boolean forest laws giving the three-bit majority spectrum consists of point masses, with label cost two bits. | Does not refute a universal $`O(I)`$ mixture cost. |
| [Tree projection](mixtures-and-obstructions.md#4-tree-approximation-the-correct-identity-and-an-exact-nonrealizable-tree) | $`H(q_T)-H(p_f)=D_2(p_f\Vert q_T)`$ and equal expected weight, including zeros. Majority's tree projection is not Boolean-realizable. | Matching marginals do not permit the Boolean forest theorem to be applied to $`q_T`$. |
| [Selector closure obstruction](interpolation.md#7-what-failed-what-is-retained-and-what-remains-open) | A balanced four-bit gate gives dyadic Boolean examples with $`H/I>4`$; a 257-input character-payload selector has $`H-4I=1/8`$. | Does not refute FEI with a larger constant. |
| [Hard-zero energy obstruction](positive-forests.md#4-a-stronger-entropy-payment-really-fails-when-zeros-are-admitted) | Actual Boolean star spectra violate the proposed positive-tree energy extension to forbidden states. | The displayed examples satisfy FEI. |
| [Integer constant-four obstruction](integer-forests.md#8-failed-constant-four-and-verification-controls) | A ternary two-bit function has raw entropy/influence ratio $`3+(9/4)\log_2(16/9)>4`$. | Does not contradict the Boolean forest theorem. |
| [Cyclic proof barriers](cycles-and-cacti.md#7-scope-examples-and-next-obstruction) | A Boolean $`K_5`$-facet witness defeats unrestricted modular lifting; a path-square graph defeats the tested cutset component payment. | Neither is a Boolean counterexample to the stated cactus theorem or to FEI. |

## Boundaries of this catalogue

All these mathematical statements are unconditional under their displayed
hypotheses and the explicitly cited classical theorems. Computations
confirm examples and bounded test ranges; they are not substitutes for
the proofs. The universal conjecture and the narrower unresolved targets
are stated separately in [OPEN_PROBLEMS.md](OPEN_PROBLEMS.md).
