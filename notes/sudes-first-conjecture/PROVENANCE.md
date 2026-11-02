# Provenance and review status

## Scope

This public note presents Sude's First Conjecture and the existing proof of
its eventual form. It is maintained as Mira-Cult research. The conjecture
for every positive odd order is distinguished from the eventual theorem in
both the [main note](README.md) and the [proof](proof.md).

## Source revisions

The mathematical source is the prime-line-sums manuscript set in
`Mira-Cult/math-wip` at scientific revision
`4ac266e7c4994a8502eb2a0c57d6b1d3fbd801c5`.
Its recorded scientific tree is
`69bf80823fb4e0ac8e453da9f7fadf2cf9c82434`.

| Public file | Source manuscript in `problems/prime-line-sums/manuscripts/` | Source Git blob |
|---|---|---|
| [proof.md](proof.md) | `eventual_prime_squares.md` | `4196402379f0bffd6ecba5c4c1a347f0a3ac0a24` |
| [controller.md](controller.md) | `reservoir_continuation.md` | `529a50b6c79e3a4aaee107c110d0578b64cfcd04` |
| [prime-targets.md](prime-targets.md) | `analytic_continuation.md`, analytic source contract and A1–A4 | `03fe617eef96571736824237ecf1264a7a813ac3` |

Review status was checked against delivery revision
`1fd32e2c81d422d3e7e0c6ba69934c84ad0a612c` of the source repository,
whose review record identifies that same scientific revision.
These identifiers locate the source history; the public mathematical argument
is contained in this note and its cited primary literature.

## Adaptation for this note

The component proofs retain their mathematical hypotheses, constants and
quantifiers. In particular, the controller retains its all-large-scale
quantitative seed argument, depletion and placement bounds, residue repairs
and centered completion. The analytic component retains the complete
fixed-class derivation, including prime powers and bounded filtering costs,
and the exact-total prime-vector lemma uniform in vector length.

Introductions and links have been rewritten for a standalone public note.
Repository workflow material and numerical replay instructions are not part
of this exposition. Mathematical notation is formatted for GitHub Markdown.
The conjecture is stated for all positive odd orders; the proof is explicitly
limited to sufficiently large odd orders.

One elementary simplification has been added to the synthesis: since
$\mu\le nX$, $X\ge n^2$ and $K\ge n^{2/3}$, its capacity inequality (P3)
already follows for every $n\ge3$ from

$$
\frac{\mu^{3/5}}{KX}\le n^{-13/15}<\frac25.
$$

This removes an unnecessary threshold from that comparison only. It does not
make the overall existence threshold numerical or change the theorem's scope.

## Review boundary

The pinned source reports internal reviews by reviewers other than the
component authors, covering the universal controller, the analytic
prime-target arguments and their synthesis. Those reviews found no remaining
blocking mathematical gap. They are internal mathematical reviews, not
anonymous external peer review or formal proof-assistant verification.

The proof remains open to public scrutiny. Its analytic imports retain their
stated hypotheses. Checking how an imported theorem is used is not a claim
that its entire published proof has been independently reproved here.
No numerical value of $n_0$, external acceptance or novelty claim is asserted.
