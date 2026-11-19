# Fourier entropy–influence: uniform bounds on structured interactions

**Mira Cult · 16 November 2026**

The strongest new theorem proves **the sharp constant four** for a recursive
class with unbounded numbers of simultaneous truth-value changes, unbounded
depth and branching, and spectra that can require unbounded interaction
arity. The proof pays signed Fourier interference and its pair terms.

For any fixed integer $`q\ge2`$, start with rare-point leaves on at least two
coordinates, each carrying $`q`$ distinct marks including its exceptional
point. At every node take $`m\ge2+\lceil\log_2q\rceil`$ disjoint children,
form their product, and flip the $`q`$ concatenated marked points. Marks
project distinctly in every child; the same $`q`$ is used throughout a
construction. The resulting functions have positive spectrum and satisfy

```math
\boxed{H(f)\le4I(f).}
```

The single constant applies to the union over **all** allowed $`q`$.
It is optimal separately for every fixed $`q`$, even when an internal node
is required. The [complete rare-leaf proof](marked-rare-leaves.md) uses the
[marked-set invariant](marked-set-closure.md), which also closes any
positive Boolean leaf class with constant $`C_0`$ at constant
$`(5/4)C_0+7`$, paid once. This gives 12 for constant-four leaves, below
24.5 for the earlier positive width-two class, and below 28 for positive
affine-forest leaves.

Two complementary structural theorems give constant four for stated
[directed integer factors](directed-factors.md), and a constant below
seventeen for [affine images of positive Boolean forests](affine-forests.md).
These hypotheses also allow interaction size to grow without bound.

**General FEI remains unresolved.** No paid representation places arbitrary
Boolean functions in these classes. The [support-completion proof](positive-support.md)
does establish exact same-constant equivalence between unrestricted FEI
and FEI for all positive Boolean spectra. New [representation barriers](approximation-barriers.md)
show why ordinary coordinate certificates and pointwise approximate
spectral norm cannot provide a universal cost proportional to influence,
even inside the new constant-four class.

The [catalogue](CATALOGUE.md) states precise scopes; [verification](VERIFICATION.md)
pins the scientific revisions, exact/certified checks and nonauthor model
reviews. These are complete conventional arguments under their hypotheses,
not formal verification, human peer review, or a universal proof.

## The question and conventions

For a Boolean function $`f:\{-1,1\}^n\to\{-1,1\}`$, write

```math
f(x)=\sum_{S\subseteq[n]}\widehat f(S)\chi_S(x),
\qquad \chi_S(x)=\prod_{i\in S}x_i,
\qquad p_f(S)=\widehat f(S)^2.
```

The measure on inputs is uniform, so Parseval gives $`\sum_Sp_f(S)=1`$.
We use bits of entropy and the usual sign-flip influence:

```math
H(f)=\sum_Sp_f(S)\log_2\frac1{p_f(S)},
\qquad I(f)=\sum_S|S|p_f(S)
=\sum_i\Pr[f(x)\ne f(x^{\oplus i})].
```

Zero coefficients contribute zero. Constants have $`H(f)=I(f)=0`$.
Identifying sign inputs with binary inputs by $`x_i=(-1)^{z_i}`$ changes
neither quantity. Walsh integers in the proofs are
$`W_f(S)=2^n\widehat f(S)`$. For real-valued sections, influence means
$`\sum_i\mathbb E((h(x)-h(x^{\oplus i}))/2)^2`$; their raw spectral
entropy is explicitly defined and need not be nonnegative.

FEI asks for one absolute constant $`C`$ such that $`H(f)\le CI(f)`$ for
every Boolean function. Constant four cannot work universally: Hod's
explicit constructions require $`C>6.454784`$ [Hod17]. This is a known
lower bound, not a claim about the current optimal lower-bound record.

## What the proofs achieve

### One constant across unbounded interactions

| Class | Uniform constant | What permits unbounded interaction size |
|---|---|---|
| [Rare-point marked-set recursion](marked-rare-leaves.md) | $`4`$, optimal for every fixed $`q`$ | Any fixed $`q\ge2`$, exception-marked rare leaves, distinct projections, $`m\ge2+\lceil\log_2q\rceil`$ at every node; no dimension, depth or arity loss. |
| [General marked-set closure](marked-set-closure.md) | $`(5/4)C_0+7`$ | The same construction for a positive Boolean leaf class with $`H\le C_0I`$. One constant across all allowed $`q`$, paid once. |
| [Directed integer factors](directed-factors.md) | $`4`$ | Every factor has at most one outgoing decrease at each state; its arity and overlap with other factors are unrestricted. A precisely charged one-atom repair is included. |
| [Affine images of positive forests](affine-forests.md) | $`4+4/\log_2(5/4)<17`$ | Arbitrary injective affine spectral maps preserve enough independent fair directions. The image can require arbitrarily large cliques. |
| [Recursive rare-point modifications](point-modifications.md) | $`9/2`$ | Arbitrary branching, leaf sizes and depth, with a disjoint product followed by one marked truth-value flip at each node. |
| [Closure of a controlled leaf class](point-modifications.md) | $`(3/2)C_0+17`$ | Positive Boolean leaves with a proved constant $`C_0`$ can be recursively combined without further depth loss. Constant-four leaves give $`23`$. |
| [One-level point modification](one-point-products.md) | $`4`$, optimal for this class | Arbitrarily many unequal rare-point blocks; the positive spectrum necessarily has full interaction arity and complete minimal graph. |

All relevant positivity, integrality, scalar, support and construction
hypotheses are part of the linked statements. The directed theorem is
stronger as a raw-entropy statement for real functions with the displayed
actual integer amplitude factorization; it is not an assertion about
arbitrary integer tensors normalized into Boolean spectra.

The affine theorem's key structural assertion is

```math
 d\le\left(2+\frac{2}{\log_2(5/4)}\right)q,
```

where $`q`$ counts independent fair spectral bits in a positive Boolean
forest law on $`d`$ variables. An affine injection retains at least $`q`$
fair coordinate marginals, so its influence is at least $`q/2`$.
The integer-tree estimate behind this is $`Z\ge2\,5^\kappa`$, proved with
two accompanying field-comparison inequalities.

The recursive theorems keep signed Fourier interference. A marked-set flip
has an exact entropy change equal to a signed score minus relative entropy.
Fourier pair terms and edges between marked physical inputs are retained.
Distinct projections give a product cancellation; Walsh integrality and a
geometric child-to-parent margin pay the correction after the flip. The
rare-leaf improvement retains a further exact cancellation before using
cube edge bounds. Replacing each child by its Boolean output loses its
marked-point data, so one-output-per-child composition cannot simply be cited.

The explicit prefix/bent witnesses in the directed and affine notes already
have flat-packet bounds; their large graphs alone do not establish novelty.
The structural theorems cover all compatible Boolean signings under their
stated hypotheses. The two-bit-leaf full-interaction witness also has a simple entropy/dimension bound. Standard results cover some small one-level cases.
The [references](REFERENCES.md) distinguish these overlaps from the stronger
uniform statements and record the limits of the priority search.

### Positive support is enough only if the bound is uniform over all laws

For an arbitrary Boolean function, add dummy inputs and change one truth
value. Every Walsh numerator becomes two modulo four, giving actual full
support. The changes in entropy and influence vanish as the number of dummy
inputs grows. The [completion proof](positive-support.md) therefore gives
an exact same-constant equivalence between unrestricted FEI and FEI for all
positive Boolean spectra. It does not preserve a low-width or other special
representation, and does not prove the missing bound.

### Positive bounded treewidth has a paid local entropy bound

For every integer-valued function with a positive Fourier law of treewidth
at most two, [the main theorem](bounded-treewidth.md) gives

```math
H_{\mathrm{raw}}(h)\le C_2 I(h),\qquad
C_2=\frac{2(2+\log_2 23)}{\log_2(23/12)}
=13.9006301761\ldots<14.
```

For Boolean functions, raw entropy is the usual Fourier entropy. The
stronger integer statement permits actual integer-valued spectral sections without
pretending they are Boolean. Positive clique potentials on triangle bags
are included; neither dyadic magnitudes nor bounded Fourier degree is
required. Every fixed width has an explicit dimension-independent bound.

Exact gcd elimination produces integer factors on the bags. The local
entropy inequality retains a term paid by the bit-one endpoint, which
sums to coordinate influence. Its nine exceptional cases are exact
integer comparisons. At bag size three this yields

```math
D_2(p\Vert U_n)\le\frac{15}{16}\mathbb E_p\log_2|W_h(S)|
+2\mathbb E_p|S|.
```

Comparison with a biased product distribution then proves the entropy
bound. The [connected triangle construction](connected-triangles.md)
has genuine cubic interactions and feedback vertex number growing without
bound. It proves strictness of the spectral class; its explicit examples
already have other FEI proofs.

### A forbidden pair can remove a denominator cost

If a two-bit spectral pattern never occurs for a Boolean function, its
four sections on that pair form an integer signed partition. Their raw
entropies add exactly. The [zero-edge theorem](zero-edges.md) combines this
fact with the dyadic integer-forest theorem for a Boolean parent whose
Fourier law itself factors over a forest, giving

```math
H(f)\le4\sum_{k\notin\{i,j\}}\mathrm{Inf}_k(f)
```

when the nonzero sections reduce to positive forest laws. The extra scope
permits nonproduct forest sections; the product-leaf special case already
had constant four. A six-bit Boolean forest shows that a second forbidden
pair can produce half-integer sections. This explains the remaining
lattice cost rather than silently iterating the first cut.

### Cycles can pay for their own conditioning

A positive pairwise law has the form

```math
p(s)=Z^{-1}\prod_i\psi_i(s_i)\prod_{ij\in E(G)}\psi_{ij}(s_i,s_j),
\qquad \psi_i,\psi_{ij}>0.
```

“Pairwise” is essential: arbitrary three-variable potentials on triangle
bags are not included. A cactus is a graph in which each edge belongs to
at most one simple cycle. The [cycle and cactus theorem](cycles-and-cacti.md)
proves $`H(f)\le4I(f)`$ for these models, and for graphs with a common
feedback vertex.

The proof first uses signed Boolean arithmetic and cut-polytope cycle
facets to exclude odd prime factors from the Walsh magnitudes. It then
conditions on a spectral feedback set. The remaining integer forest
sections have a strict entropy deficit for each nonconstant component.
For a cactus, the feedback set can be chosen so that those components pay
the entire conditioning denominator cost, even as the number of cycles
grows. The full argument imports the classical Barahona–Mahjoub
cut-polytope theorem, stated precisely and cited in the proof.

The arithmetic conclusion holds for every **positive pairwise** graph of
treewidth at most two. The constant-four conclusion has only the stated cactus,
common-feedback-vertex, and paid-cutset scopes; the independent theorem above
covers all positive width-two laws with a larger constant. The square of an
eleven-vertex path is an explicit obstruction to the tested component-count
payment; it is not a Boolean counterexample to FEI.

### Integer sections retain their label cost

The [integer forest theorem](integer-forests.md) proves

```math
H_{\rm raw}(h)\le \frac{6}{\log_2(16/9)}I(h),
\qquad \frac{6}{\log_2(16/9)}=7.2282625189\ldots,
```

for integer-valued functions with positive forest spectra, without any
restriction on odd Walsh factors. Its proof factors an integer amplitude
tensor into positive integer edge factors and applies the cube logarithmic
Sobolev inequality in the spectral variables. A concentration argument
then removes the additive lattice loss for Boolean functions whose spectra
become positive forests after a bounded number of spectral conditioning coordinates.
The resulting constant depends on that bound, and not on ambient dimension.

The [dyadic version](spectral-conditioning.md) has constant four and a
component deficit. It allows unbounded amplitude spread but requires each
nonzero magnitude to be an exact power of two. Raw entropies add over
disjoint Fourier sections, including the component-mass entropy. This
is why actual integer packets can pay a label cost that an ordinary
probability mixture leaves unpaid.

### Physical interpolation can use shared data

For a physical restriction tree stopping at functions $`g_L`$, let $`D`$
be the number of queries on a uniform input. The
[interpolation theorem](interpolation.md) gives

```math
H(f)-4I(f)\le
\mathbb E_L\bigl[H(g_L)-4I(g_L)\bigr]+\tfrac12\mathbb E D.
```

Every nonconstant admissible forest leaf has deficit at least two. Thus
four fixed controls suffice when all leaves are nonconstant forests, and
an arbitrary-length first-hit list satisfies $`H(f)\le4I(f)`$ with strict
slack. Its expected query depth stays below two. An explicit infinite family
has odd Walsh factors and cannot factor over any spectral forest.

Earlier shared-data selector identities already yield a coarser constant
bound for these lists [Shmalo26]. The contribution described here is the
half-bit influence-corrected defect and preservation of constant four.
It is not a claim that these examples were previously outside every known
FEI class. An explicit balanced gate disproves free, unrestricted
iteration of constant-four forest selection.

## Reading the proofs

The [catalogue](CATALOGUE.md) gives exact hypotheses and theorem locations.
The main proof paths are:

- **Bounded-width dependence:** [integer bag factorization and paid local
  entropy](bounded-treewidth.md), [connected triangle laws](connected-triangles.md),
  and [forbidden pairs and zero-edge barriers](zero-edges.md).
- **Sharper constant-four graphical bounds:** [forest arithmetic](forest-arithmetic.md),
  [complete positive-forest energy proof](positive-forests.md),
  [integer spectral conditioning](spectral-conditioning.md), then
  [cycle facets and cacti](cycles-and-cacti.md).
- **General integer sections:** [integer forests](integer-forests.md),
  including the local integrality defect and the near-constant section
  estimate. [Integer flat packets](integer-flat-packets.md) provide the
  earlier support-weight comparison with full proofs and attribution.
- **Physical restrictions and obstructions:**
  [half-bit interpolation](interpolation.md) and
  [Boolean mixtures and approximation](mixtures-and-obstructions.md).

[Deterministic contractions](deterministic-contractions.md) supply the
precise extension to fixed bits and equality/complement support relations.
Genuine three-state edge supports have the limited forbidden-pair extension
above; their general case remains open. The arithmetic exclusion for forests
itself does allow zeros.

All proof dependencies used in these paths are included here or cited to
specific accessible primary theorems. See [references](REFERENCES.md) for
external attribution and [reproducible checks](code/README.md) for finite
examples, certified scalar inequalities, and exhaustive small cases.

## The next mathematical problems

The [open-problems note](OPEN_PROBLEMS.md) states precise targets and the
known obstructions. The most direct opportunities are to remove the width
dependence, control the local integrality defect of a positive pairwise
Boolean spectrum, and handle arbitrary genuinely three-state forest edges.
Constant four on all positive pairwise width-two laws remains a sharper
class question after the dimension-independent endpoint was proved.
A universal integer-packet or low-information decomposition would be a
larger advance, but it must pay its denominator or label cost from Boolean
structure. Majority already forces every forest-mixture component to be
a point mass, so existence of a decomposition alone is insufficient.
