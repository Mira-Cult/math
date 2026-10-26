# Trimmed coded folding for Euclidean GapCVP

**Research note · 26 October 2026 · CVP-M10**

This note presents a deterministic reduction from sparse Boolean quadratic
satisfiability to Euclidean GapCVP. Its quantitative contribution is a
coefficient-one inverse-deficit bound on **lattice rank**, obtained by combining
packed source semantics, two-level interpolation, a sitewise binary code, and
trimmed sampling sets.

**Status.** This is an exposition of a complete mathematical **proof draft**,
not a formally verified or human-expert-reviewed theorem. The source is the
open draft PR 369 of `Mira-Cult/cvp`, frozen at commit
`1a2a2b06e1942e6938ccb8b51a33deb43f0380bb`. The selected proofs are included
locally so that readers do not need access to that private repository.
Model-assisted audits and finite regressions provide additional checks, not
proof certificates. See [provenance and verification](PROVENANCE.md).

## 1. Statement and conventions

For each **fixed rational** $0<\varepsilon<1/2$, the draft gives a deterministic
polynomial-time reduction to the following promise problem on a full-rank
lattice $\Lambda\subseteq\mathbb Z^D$, integer target $t$, and integer radius
$\rho>0$:

$$
\text{YES: }\operatorname{dist}_2(t,\Lambda)\le\rho,
\qquad
\text{NO: }\operatorname{dist}_2(t,\Lambda)>D^{1/2-\varepsilon}\rho.
$$

If $N\ge8$ bounds the variables, equations, and distinct monomials of the
sparse quadratic source, with the monomial count strictly below $N$, then

$$
D\le N^{1/\varepsilon}
 2^{(A_\varepsilon+o_\varepsilon(1))
       \sqrt{\log_2N\,\log_2\log_2N}},
\qquad
A_\varepsilon=\sqrt{\frac{2(1-2\varepsilon)}{\varepsilon^3}}.
$$

Thus $D\le N^{1/\varepsilon+o(1)}$, for fixed $\varepsilon$. The **gap is
exact**; the asymptotic error belongs to the rank bound, not the gap. The full
bit runtime, including affine-system emission, elimination, and the complete
$D\times D$ lattice basis, is $N^{O(1/\varepsilon)}$. Its exponent is not
claimed to be $1/\varepsilon$.

The source parameter is not automatically the number of SAT variables. A
3CNF of encoding length $n$ has a sparse quadratic encoding of size $O(n)$;
linear-size or polylogarithmic source conversions preserve the displayed
leading rank degree, but a polynomial source conversion must be counted.
The result is an **ordinary, instance-dependent-lattice reduction**, not a
fixed-lattice preprocessing theorem. No square-root endpoint, practical-size
implementation, optimality, or priority claim is made.

## 2. Encoding the source without assuming honest witnesses

For a clause let $a_1,a_2,a_3$ be the Boolean indicators that its literals are
false. Introduce one Boolean variable $y$ and impose over $\mathbb F_2$

$$
y+a_1a_2=0,\qquad ya_3=0.
$$

These equations hold for some $y$ exactly when the clause is satisfied. More
generally, a Boolean circuit admits constant-size gate constraints, for example
$z+xy=0$ for AND and $z+x+1=0$ for NOT; its input, witness and gate-wire counts
must all enter the source-size ledger.

Use compatible characteristic-two fields

$$
F=\mathbb F_q\subset H=\mathbb F_{q^h}\subset
B=\mathbb F_{q^{h\ell}}\subset E=\mathbb F_{q^n},
\quad n=4h\ell,
$$

where $h\ge2$ and $\ell\ge2N$ are powers of two. These fields and power bases
can be built explicitly by quadratic towers. Enumerating all of $E$ is not
required.

List the source monomials $x_{i_k}x_{j_k}$ and choose distinct $\xi_k\in H$.
Interpolate $A_x(Y),B_x(Y)$ with respective values $x_{i_k},x_{j_k}$.
Their ordinary product has degree below $\ell$, so its coordinates in $B$
retain every monomial. Encode the assignment injectively as $T_x\in B$;
then $A_x=L_A(T_x)$ and $B_x=L_B(T_x)$ for explicit binary-linear maps.
Each source equation is an explicit binary-linear functional of
$(T_x,A_xB_x,1)$.

Choose three $B$-independent elements $\theta_0,\theta_1,\theta_2\in E$ and set

$$
\beta_x=\theta_0T_x+\theta_1A_x+\theta_2B_x,
\quad v_x=(1,T_x,A_x,B_x),\quad C_x=v_xv_x^T.
$$

Expand the sixteen ordered entries of $C_x$ in a binary basis of $B$ to
obtain a nonzero semantic vector $\sigma(x)$ of length
$C=16h\ell\log_2q$. Crucially, the source maps act **coefficientwise on these
binary channels**, not on assembled $E$-valued moments. An arbitrary
binary-linear map does not commute with multiplication by $\beta_x^e$.

## 3. The measured table and the two interpolation levels

Choose a power of two $s\ge2$ and integer $r\ge1$. Put

$$
K=s^r,\quad\Delta=(2r+4)s,\quad
d_{\rm in}=(h-1)\Delta,\quad d_{\rm out}=(n-1)\Delta,
\quad T=2d_{\rm in},\quad R=2d_{\rm out}.
$$

Require $T\le q$ and $R\le q^h$. Take deterministic distinct sample sets
$I\subset F$, $O\subset H$ of sizes $T,R$. The tuple domain remains **all**
of $F^r$.

The [explicit code lemma](proofs/CODED_CHANNELS_LEMMA.md) supplies a binary
linear injection $G:\mathbb F_2^C\to\mathbb F_2^M$ with a left inverse $R_c$,

$$
C\le M\le32C,\qquad d_{\rm code}>M/8,\qquad R_cG=I.
$$

It concatenates Reed–Solomon evaluation with a deterministically constructed
binary inner code; the latter is obtained by greedy conditional expectation
on an exact exponential-weight potential. The construction is polynomial
in $C$, without a random-code assumption.

At each $(\zeta,t,u)\in O\times I\times F^r$ introduce $M$ measured bits $w$.
Emit $w=GR_cw$ and use $z=R_cw$ as a derived linear form. The exact number of
measured coordinates—and eventual full lattice rank—is

$$
D=MRTq^r.
$$

For radix-$s$ monomials $\phi_a(u)$ (the top digit may be unbounded), form

$$
V_{\zeta,t}((a,c),b)
 =\sum_{u\in F^r}z_{\zeta,t,u,c}\phi_a(u)\phi_b(u),
\quad 0\le a<K,\quad0\le b\le4K.
$$

Let $d(a,b)$ be the sum of the radix digits of $a$ and $b$; then
$d(a,b)<\Delta$. Interpolate each entry over $I$, explicitly set coefficients
above $(h-1)d(a,b)$ to zero, and evaluate at a power-basis generator
$\omega\in H$. Interpolate these values over $O$, set coefficients above
$(n-1)d(a,b)$ to zero, and evaluate at a generator $\eta_E\in E$.

The resulting matrix is forced to be Hankel:
$H_{\rm glob}((a,c),b)=m_{a+b,c}$. Moments exist through $5K-1$.
Emit Frobenius equations $m_{2e,c}=m_{e,c}^2$ for $0\le e<K$, channel
symmetry, the identifier and coefficientwise source equations, and a mass
coordinate equal to one. With binary basis element $e_0=1$, also emit
$m_{e,0,0,k}=0$ for $k>0$ and $0\le e<K$; these ensure that each
recovered $(0,0)$ matrix entry is binary, rather than merely $B$-valued. Everything is binary affine; decoded bits,
interpolation coefficients and moments are **not additional variables**.
The exact equation list is in [the compiler](proofs/CODED_PACKED_TWO_LEVEL_FOLD.md),
Sections 4–5, with sampling replaced as in
[the trimmed compiler](proofs/TRIMMED_CODED_FOLD.md), Section 3.

Trimming means **recomputing the interpolation maps** on $I,O$, not deleting
coordinates from the old system while keeping its old maps.

## 4. Why every feasible word pays for its rank

For any polynomial matrix $A(X)$ with entry degree at most $d$, any set
$S$ of distinct field elements, and any extension-field point $\xi$,

$$
\sum_{a\in S}\operatorname{rank} A(a)
 \ge (|S|-d)\operatorname{rank} A(\xi).
$$

To prove this, choose a $t\times t$ minor nonzero at $\xi$, where
$t=\operatorname{rank}A(\xi)$. Its determinant has degree at most $td$.
At each sample its root multiplicity is at least the rank defect: constant
row operations exhibit that many rows divisible by $X-a$. Sum these
multiplicities over the distinct samples. This argument is valid in
characteristic two and does not require a full-field grid.

At a fixed sampling pair each nonzero decoded vector $z_u$ contributes one
outer product to $V$, hence rank at most one, while its codeword costs at
least $d_{\rm code}$ measured bits. Applying the rank estimate at both
levels therefore yields, for **every** feasible measured word of weight $W$,

$$
W\ge d_{\rm code}(T-d_{\rm in})(R-d_{\rm out})
        \operatorname{rank}_E H_{\rm glob}
 =\frac{d_{\rm code}TR}{4}\operatorname{rank}_E H_{\rm glob}.
$$

This is the role of the code: a whole channel vector pays its full coding
cost but is charged as only one rank contribution. There is no assumption
of an honest support, source-valid atoms, or noncancellation.

## 5. Finite Hankel atomicity and source recovery

The [finite Hankel theorem](proofs/VECTOR_HANKEL_ATOMICITY.md) is a separate,
self-contained linear-algebra argument. Applied to the emitted window, it
says that rank $t<K$ and the emitted Frobenius identities imply

$$
m_{e,c}=\sum_{j=1}^{u}\beta_j^e\sigma_{j,c},
\qquad u\le t<K,\quad0\le e\le4K,
$$

with distinct atoms in an algebraic closure and nonzero **binary** coefficient
vectors. The theorem reconstructs a protected prefix; it does not claim
that all trailing supplied moments are recovered or that $u=t$.

Here are the essential steps, which prevent an implicit atomicity assumption:

1. A row-rank plateau makes shift of available column relations well-defined.
   A column-span plateau then gives a finite state realization $M_e=CA^eB$
   on the protected prefix, of dimension at most $t$.
2. Cayley–Hamilton extends the finite Frobenius identities to the infinite
   realized sequence. The two Frobenius-defect terms satisfy the **same**
   recurrence, so their difference does not require twice as many initial
   conditions.
3. Frobenius makes the joint scalar recurrence ideal radical: if $f^2$
   annihilates the sequence, squaring and injectivity of field squaring show
   that $f$ does too. Its generator is squarefree.
4. Split the generator and use Vandermonde inversion. A second Vandermonde
   inversion at the squared roots forces every coefficient to satisfy
   $c^2=c$, hence to lie in $\mathbb F_2$.

Regroup each recovered vector into a nonzero symmetric $4\times4$ matrix
$C_j$ over $B$. Vandermonde isolation of the emitted identifier equations gives

$$
\beta_j C_j(0,k)=\theta_0C_j(1,k)+\theta_1C_j(2,k)+\theta_2C_j(3,k).
$$

If $C_j(0,0)=0$, independence of the $\theta_i$ and symmetry first kill its
first row and column and then every entry, a contradiction. Thus its binary
mass is one. The same equations imply $\beta_j\in E$ and
$C_j=(1,T_j,A_j,B_j)(1,T_j,A_j,B_j)^T$. The coefficientwise source equations
force $T_j$ to encode a genuine satisfying Boolean assignment. The global
mass equation makes the atom count odd, hence nonzero.

Consequently an unsatisfiable source forces rank at least $K$, giving
$W_{\rm NO}>MTRK/32$. A satisfying assignment yields one occupied tuple
per sampling pair carrying $G\sigma(x)$; interpolation uniqueness recovers
its exact moments and gives $W_{\rm YES}\le MTR$.

## 6. Exact parity-kernel lattice handoff

Write the emitted system as $Aw=b$. If it is consistent choose a binary
solution $w_0$ and set

$$
\Lambda=\{v\in\mathbb Z^D:A(v\bmod2)=0\},\qquad t=w_0.
$$

Then exactly

$$
\operatorname{dist}_2(w_0,\Lambda)^2
 =\min\{\operatorname{wt}(w):Aw=b\}.
$$

For one direction, every odd coordinate of an arbitrary integer residual
costs at least one in squared norm. For the other, a feasible binary $w$
gives the lattice vector $w_0-w$. Thus the soundness statement covers **all
integer representatives**, including negative or large coordinates.
Binary elimination produces a full-rank basis with entries in $\{0,1,2\}$.
Code membership does not reduce its integral rank.

Set $\rho=\lceil\sqrt{MTR}\rceil$. Since $\rho^2\le4MTR$, the NO/YES ratio
is strictly greater than $\sqrt{K/128}$. Therefore it suffices to enforce
$K>128D^{1-2\varepsilon}$. If the affine system is inconsistent, output
the explicit strict-NO lattice $2a\mathbb Z^D$ with target $ae_1$, where
$a=(D+1)\rho$; this branch cannot occur for a satisfiable source.

## 7. The trimmed parameter schedule

All logarithms here are base two. Let $\lambda=1-2\varepsilon=A/B$ in lowest
terms, $L=\lceil\log N\rceil$, $G_0=\operatorname{bitlength}(L)$ and
$W_0=\operatorname{bitlength}(\max(1,\lfloor L/G_0\rfloor))$. Fix

$$
r=\max\left(2,\left\lceil4\lambda/\varepsilon\right\rceil,
 \left\lceil\sqrt{2\lambda L/(\varepsilon W_0)}\right\rceil\right).
$$

Search $1\le k\le L$. For each candidate let $h$ be the least power of two
at least $\max(2,\lceil(L+4)/k\rceil+1)$, put
$b_0=\lceil\log(4(h-1)(r+2))\rceil$, and use $q=2^k$, $s=2^{k-b_0}$.
Reject $k\le b_0$. For valid candidates, the actual field bounds follow
from these definitions and

$$
D\le D_*:=hk\,2^{2L+14+(r+2)k}.
$$

Accept the first candidate with $K>128D_*^\lambda$. This is an exact
integer test, including strictness:

$$
[r(B-A)-2A]k\ge7B+A(2L+14)+rBb_0+
 \operatorname{bitlength}((hk)^A).
$$

The acceptance predicate is monotone, so bounded binary search suffices.
The [parameter proof](proofs/TRIMMED_FOLD_PARAMETERS.md) supplies a computable
cutoff beyond which a candidate always exists. Below it the source may be
decided directly; for fixed $\varepsilon$ this contributes only a finite
constant to runtime, not an efficiency recommendation.

The asymptotic balance is

$$
\log D\le\frac{L}{\varepsilon}
 +\frac{\lambda}{\varepsilon^2}\frac{L}{r}
 +\frac{rW_0}{2\varepsilon}+O_\varepsilon(r+\log L).
$$

Choosing $r^2\sim(2\lambda/\varepsilon)L/W_0$ gives the constant
$A_\varepsilon$ above and, more sharply,

$$
\log D\le\frac{L}{\varepsilon}
 +A_\varepsilon\sqrt{L(\log L-\log\log L)}
 +O_\varepsilon(\sqrt{L/\log L}+\log L).
$$

At identical old parameters the exact rank saving over full-field sampling
is $q^{h+1}/(RT)$, with the code and $K$ unchanged. This is a comparison of
dimension formulas, not a constructed-lattice benchmark.

## 8. Reading and checking the proof packet

The dependency chain is:

- [Source, identifiers, coefficientwise decoding and parity lift](proofs/CODED_PACKED_TWO_LEVEL_FOLD.md), Sections 3–5 and 8–9.
- [Explicit code and left inverse](proofs/CODED_CHANNELS_LEMMA.md).
- [Finite Hankel extraction](proofs/VECTOR_HANKEL_ATOMICITY.md).
- [Recompiled trimmed tables and all-witness rank charge](proofs/TRIMMED_CODED_FOLD.md).
- [Exact parameter selection and bit complexity](proofs/TRIMMED_FOLD_PARAMETERS.md).

These five files are source-pinned mathematical proofs, reproduced without
content edits. Historical cross-references in them are documented in
[PROVENANCE.md](PROVENANCE.md); they do not add unpublished assumptions to
the dependency chain above. The accompanying finite scripts test selected
algebraic and arithmetic consequences, not the entire asymptotic compiler.

## 9. Relation to Fenzi–Weissenberg and earlier moment methods

Fenzi and Weissenberg's [*Nearly Optimal Hardness for CVP and NCP with Preprocessing*](https://eprint.iacr.org/2026/2634) (25 October 2026 version)
proves a stronger **fixed-lattice** form of the near-square-root hardness
statement. Their deterministic construction is unconditional: the lattice
and radius depend only on input length, while the formula determines the
target. Complexity assumptions enter the consequences excluding efficient
algorithms with preprocessing, not the construction's correctness.
Their work also treats arbitrary fixed finite fields for NCP and all norms
for CVP. This note does not claim those extensions.

Their paper credits the earlier OpenAI moment method and Song's improvements.
The headline ordinary binary Euclidean hardness exponent is therefore not
claimed as new here. Determinant rank estimates and Frobenius moment
extraction are shared antecedent techniques. The specific contribution under
discussion is the **certified rank ledger** of the packed, coded, trimmed
construction above.

For a quantitative comparison, use a common sparse verifier/gate-system size
$N$ and count any source-conversion overhead explicitly. Appendix A.4,
equation (37) and its following bound, gives the published estimate

$$
n_{\rm sys}\le C_a(N+1)^{a+5+2/a}\Gamma^{1+1/a},
$$

for fixed integer folding parameter $a\ge1$. Theorem 5.1 converts this to
lattice dimension $M$ with $2n_{\rm sys}\le M<4n_{\rm sys}$ and uses, in
the Euclidean case, the sufficient condition
$\Gamma>16M^{1-2\varepsilon}$. Setting $\Gamma=N^g$ and allowing strict
exponent slack yields the following **sufficient degree threshold derived
from those displayed bounds**:

$$
P_{\rm FW}(a,\varepsilon)
 =\frac{a^2+5a+2}{2\varepsilon a-(1-2\varepsilon)},
\qquad 2\varepsilon a>1-2\varepsilon.
$$

Indeed, if $P=a+5+2/a+(1+1/a)g$, one needs $g>(1-2\varepsilon)P$;
eliminating $g$ gives the expression. Constants are absorbed by choosing a
degree strictly above the threshold. Optimizing this expression over real
$a$ gives

$$
P_{\rm FW}^{\rm real}(\varepsilon)
 =\frac{1+3\varepsilon+\sqrt{1+6\varepsilon-8\varepsilon^2}}
        {2\varepsilon^2}.
$$

Integer optimization has the expansion
$\varepsilon^{-2}+3\varepsilon^{-1}+O(1)$ as $\varepsilon\to0$.
This is a comparison of **certified upper-bound ledgers**, not a lower bound
on their construction, a claim about its actual minimal dimension, or an
obstruction to improving their analysis. Our draft instead certifies leading
rank degree $1/\varepsilon+o(1)$ as $N\to\infty$ for each fixed rational
$\varepsilon$. Smaller ordinary-reduction rank does **not** imply an equally
small fixed-lattice reduction.

The proof-status comparison also matters. Fenzi–Weissenberg report Lean
verification of the mathematical content underlying their main reduction;
the [formalization scope](https://github.com/WizardOfMenlo/preprocessing-approximations-lean/blob/4cf4407992ed0da71f58b17c1e7ab2360a3541cc/README.md)
excludes polynomial-time computability and the complexity-theoretic wrapper.
Our latest refinement is a mathematical draft with model-assisted reviews
and finite regressions, not a Lean certificate. We did not rebuild their
Lean development during this review. No blanket claim that one
result is “better” is justified by a single dimension comparison.

**Possible compositions are not release theorems.** Replacing the scalar
moment representation in their preprocessing framework by two-level tables
is a plausible further direction. The needed interface includes finite-field
linearity, homogeneous constraints, coefficient-field membership, moment
horizons and all-witness support bounds—not merely a matching exponent
calculation. Likewise, all-norm adaptations require a separate conversion
and resource proof. This release proves neither a hybrid preprocessing
bound nor an all-norm extension of the displayed coefficient-one theorem.
