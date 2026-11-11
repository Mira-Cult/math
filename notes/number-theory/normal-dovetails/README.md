# Normal dovetails: analytic functions and constructed numbers

A connected account of the Mira-Cult dovetail work, from the older logarithmic constructions to the coefficient-window theory. Public proof-source release, 11 November 2026.

The main result constructs a normal digit stream by concatenating complete fractional prefixes of function values at a shrinking sequence of rational inputs. It works for nonpolynomial real D-finite functions, including rational, algebraic and transcendental examples. The proofs retain every row and control every output prefix, not just selected stage endpoints.

## Read the mathematics

- **[Main manuscript](MANUSCRIPT.md):** full coefficient-window proof, common schedules for real D-finite germs, exact power exceptions, and the rational-derivative admission dichotomy. Includes the precise imported derivative estimate and a proof of the Fourier-to-word estimate.
- **[Transfer and obstructions](TRANSFER_AND_OBSTRUCTIONS.md):** the older logarithmic CRT grid, the necessary source-count bound, a sufficient shifted-orbit transfer theorem, analytic interpolation rigidity, and the classical normal Liouville construction.
- **[Further producer-proof drafts](EXTENSIONS.md):** singular powers, normalizing selected flat functions by changing the schedule, and the exact near-polynomial parameter scale. These retain their stated review limits.
- **[History and open directions](HISTORY.md):** how the older and newer results fit together, and which recent branches are not part of this release.
- **[References](REFERENCES.md), [provenance](PROVENANCE.md), and [verification](VERIFICATION.md).**

## What the main theorem says

Fix an integer base $b\ge2$. At stage $r$ retain every $b^{r-1}\le j<b^r$, set

$$x_j=(bj+1)b^{-A_r},\qquad K_r=A_rD_r,$$

and copy the **complete first $K_r$ canonical fractional base-$b$ digits** of $h(x_j)$. Terminating expansions are used at ambiguous endpoints. No favorable fragment, row subset, or reordering is allowed.

If the derivative coefficients of $h$ obey the upper and finite-window lower bounds in the manuscript, there is a schedule with

$$A_r/r\longrightarrow1,\quad D_r\longrightarrow\infty,\quad x_j\longrightarrow0,$$

whose concatenation is normal. For any computable nondecreasing divergent integer budgets $F,G$, it can also satisfy

$$K_j\le F(j)\log_bj,\qquad A_j-\log_bj\le G(j)$$

eventually. Every fixed word has discrepancy $O(NB_r/(rD_r))$ through every output prefix, with $B_r=A_r-r$ and $r$ the last observed stage. The constants and onset depend on the coefficient-window data. The theorem gives a common schedule on a common-radius class; a uniform error estimate over parameters requires shared bounds and nondegeneracy.

Nonpolynomial D-finite germs satisfy the window hypothesis. Examples include $\log(1+x)$, $x/(1-x)$, $\sqrt{1+x}$, $e^x$, and $\sin x$. This is not a claim that their individual values at the sampled inputs are normal.

## Why transcendence is not the admission criterion

For rational derivatives regular at zero, admission uniformly over all additive centers is equivalent to **nonpolynomiality**, not to transcendence of the primitive. Earlier globally bounded-function obstructions concern a specific large-precision schedule and remain useful at that scope. They do not contradict the newer rational-function examples.

The exact exceptions for $(1+x)^\alpha$ are $\alpha=0,1,2,\ldots$; for $(1-x)^{-\theta}$ they are $\theta=0,-1,-2,\ldots$. These parameters turn the source into an integer-coefficient polynomial with overwhelmingly zero deep digits. Nonexceptional fixed parameters share one schedule, but convergence need not be uniform near an exceptional parameter.

## Limits and verification

These are theorems and proof drafts about **constructed streams**. They prove neither normality of their centers nor normality of unchanged $\log2$, $\pi$, or $\zeta(3)$. The main construction is for each fixed base, not an absolute-normality theorem. A computable schedule does not by itself make the copied digits computable for arbitrary real input data. This construction does not establish that the resulting number is transcendental.

The proof source has received a fresh scoped nonauthor model review and exact finite replay, described in [VERIFICATION.md](VERIFICATION.md). No formal proof, external expert/referee acceptance, historical priority, or universal optimality is claimed. Publishing the source is separate from settling these questions.

Run the source checker with Python 3.10 or later:

```sh
python3 -B verify_finite.py
python3 -B -O verify_finite.py
```

Its 1,332 finite cases test exact identities and boundary conventions. They do not prove an infinite normality theorem.
