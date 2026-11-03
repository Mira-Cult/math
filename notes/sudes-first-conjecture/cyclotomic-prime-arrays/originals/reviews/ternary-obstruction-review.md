# Independent review of the ternary cube obstruction and next-order example

Reviewer: `/root/controller`.
Review date: 2026-11-03.
Reviewed supplemental commit: `3fe1dfbcec2e2c500ac974081f0f5eda8b9e344d`.
Earlier scientific source, unchanged by this supplement:
`d9bd9ac92851a9996c14dd2fdf49f1879bcae97b`.

## Exact scope and authorship

I read the complete supplemental manuscript, the generator, both replay/checker
implementations, the finite tree, and the positive K9 certificate. The reviewed
commit exists locally. The following SHA-256 values bind the exact frozen
bytes; paths are relative to `problems/cyclotomic-prime-arrays/`.

| Source | SHA-256 |
|---|---|
| `manuscripts/ternary_cube_obstruction.md` | `3e9f58ec0d8c8bf109d63494550b1360aa1119d024f33b11121e3e61abc02ecf` |
| `code/generate_ternary_cube_obstruction.py` | `63f019bf75fadb4ecff1014c7e6fc4620a07f863ec10f6baeb174ea2a186c0ab` |
| `code/replay_ternary_cube_tree.py` | `28368daed16c80143c26984f1fa542c5d87df69ad89b14561e864b2dcb19a804` |
| `code/check_ternary_cube_obstruction.py` | `7ccff9d3d22a39c0b5cc409a716750678f556d69697fc7bd21c1a25adace7da8` |
| `inputs/ternary_cube3_unsat.json` | `dd55e8f59cf73c47afce579e413d7572d744485c06feeeaecf636efa3ab316b9` |
| `inputs/energy_m9_cube4.json` | `63026669c57fd3e68b59b4e1ec2dba41ae3beb59cc6975f68e1c158a93752919` |

The normalization agent authored the manuscript, generator, and author replay.
The coordinator authored the separate independent checker and separate search.
I authored none of those four sources. The shared authorship of the first
generator/replay pair is accurately disclosed; separate implementations alone
are not represented as independent authorship.

I authored the earlier `check_energy_certificate.py`, so that checker is
**excluded from independent acceptance by this review**. Its use below is
disclosed verification of another author's new certificate; another reviewer
has the separate obligation to review my checker source. No claim about the
eventual controller is independently reviewed here. This is an internal
mathematical/source review, not external refereeing, a formal proof-kernel run,
a novelty judgment, a CI result, or an integration approval.

## Arithmetic proof: TC1 and TC3

No blocking issue was found in the universal arithmetic argument.

For `c=3^a`, I checked that
`rho=-zeta_c^((c+1)/2)` has first argument `pi/c`, that
`beta=1+rho=1-zeta_c^((c+1)/2)` has norm three, and that beta generates the
unique totally ramified prime P. The exponent `(c+1)/2` is coprime to c.
These calculations agree with the prime-power cyclotomic integral-basis,
ramification, and torsion facts in Milne,
[Algebraic Number Theory, v3.08](https://www.jmilne.org/math/CourseNotes/ANT.pdf),
Chapter 6, Theorem 6.4, Remark 6.6, and the prime-power unit discussion in
Proposition 6.7. I inspected these primary-source passages during the same
day's general-source review, and rechecked their applications here.

The full-unit assertion does not assume convenient real units exhaust the
unit group. For any unit u, `u/conjugate(u)` is an integral unit with all
embedding absolute values one and hence is torsion. Equivalently, all its
powers lie in a fixed bounded part of the Minkowski lattice, so two powers
coincide. If its torsion exponent were odd, a root-of-unity adjustment gives
`v/conjugate(v)=rho`. Then `v/beta` is in the real subfield but has P-valuation
minus one. Restriction of valuations from K to its maximal real subfield
has even values because the relative ramification index is two. This is a
contradiction. Even torsion exponent gives the claimed real unit after a
torsion adjustment, including integrality of its inverse.

Consequently every beta-associate has first phase `theta mod 2theta`, with
`theta=pi/(2c)`. None lies in the open sector. An integral element on either
boundary, divided by beta or its conjugate, is real and has an odd integral
P-valuation; it is therefore divisible by P. A prime boundary element must
be the ramified class, which the pool excludes. This handles all infinitely
many associates, including those of arbitrarily large height.

The strict sector is an open additive cone with positive first real part.
Every nonempty ordinary sum of retained entries remains in it and is nonzero.
A sum divisible by P cannot be a unit; if prime, it would generate P and be
a beta-associate, already excluded by the phase argument. Thus divisibility
is converted into nonprimality with the exceptional-associate issue fully
resolved. No balancing of the sum, norm-growth assertion, class-number-one
assumption, or large-coordinate argument is used.

Finally every retained entry is one of the two nonzero residues modulo P.
For a triple of signs, the residue sum in F3 is zero exactly for three equal
signs. TC2 therefore supplies a required line whose sum satisfies the preceding
nonprimality argument. The conclusion is correctly stronger than a statement
about one initial pool: it holds for any 27 unramified prime elements in the
specified first sector, irrespective of ordering, size, or distinctness.
The extension of TC1 alone to other odd prime-power conductors is also valid;
the subsequent two-color reduction specifically uses residue field F3.

## Finite proof: TC2 and the programs

The line families were checked from their definitions. A full length-three
line has opposite endpoints whose coordinate differences lie in `{0,2,-2}`;
their midpoint is the third grid point. This reconstructs exactly 27 axes,
18 slice diagonals, and four bodies. The row-major index is `9*x+3*y+z`, so
cell 13 is the center. The generator's signed-direction enumeration and the
checkers' endpoint-pair enumeration describe the same 49 lines.

The finite inference rules are sound and exhaustive:

1. Global color exchange permits the single root assignment at the center.
2. Two equal assigned colors on a line force the unassigned third cell to
   have the opposite color in every valid completion.
3. Each branch selects a genuinely unassigned cell and includes both colors.
4. Each leaf displays a reconstructed required line with three assigned,
   equal colors.

Induction upward through the finite tree proves there is no extension of the
root, and color exchange covers every coloring. Both replay implementations
copy inherited states at the appropriate branches, reject overwriting forced
cells, verify every actual premise, require both children, and check the
monochromatic conflict itself. Their strict node-shape checks prevent treating
an incomplete branch as a proof. The independent checker's additional search
is a distinct exhaustive propagation/branching implementation and consumes no
tree certificate. Its failure is not needed once the displayed tree is checked.

Observed exact results:

* Regenerating the certificate reproduced its bytes and displayed SHA-256
  exactly.
* The author replay verified 49 lines, 31 nodes, 15 branches, 16 conflicts,
  220 forced assignments, and maximum depth five; both of its adverse
  controls were rejected.
* The independent checker obtained the same tree statistics and rejected
  all eight named adverse controls. It uses 47 of the 49 available lines
  in this particular proof. That is sufficient: an unsatisfiable subset
  of required constraints proves the whole system unsatisfiable. It is not
  a missing-diagonal error.
* The separate independent search exhausted 15 nodes and eight conflicts.
* I additionally changed a leaf conflict to the genuine required line
  `(0,1,2)` which was not monochromatic in that leaf's actual assignment.
  The independent checker rejected it as nonmonochromatic. This exercises
  the conflict-value check, beyond merely rejecting a nonexistent line.

No defect was found in the generator, the author replay, the independent
checker, or the inference from the retained explicit tree. The mathematical
certificate is the complete assignment tree, not an unverified solver status.

## Exact K9 prefix and the positive next order

Using the previously frozen energy checker, I independently reproduced the
manuscript's first-27 arithmetic data: energy bound 18 gives 2215 integral
ellipsoid points; all 31 unramified prime ideals through norm 127 are covered;
the ordered first 27 have residues eleven `+1` and sixteen `-1` modulo P.
This is exactly the first 27 entries of the new 64-entry certificate's pool.
The universal obstruction does not depend on these particular counts.

The new order-four cube certificate verifies in the unchanged energy model:

| Checked quantity | Value |
|---|---:|
| Prescribed initial entries | 64 |
| Norm cutoff | 307 |
| Contributing prime ideals through cutoff | 64 |
| Energy bound | 24 |
| Integral ellipsoid points | 4951 |
| Required prime line sums | 76 |
| Rejected fixture mutations | 15 |
| Common exact arithmetic controls | 50 |

Every one of the 76 line sums has residue degree one in this example. Pool
enumeration still uses the complete prime-element criterion and does not
discard higher-degree input primes. The fixture digest reported by the
independent arithmetic implementation is
`b5e00f771055537ac309e4969f5ce407446deb811fd2a0d98acce683ea29b5da`.
This differs intentionally from the SHA-256 of the JSON bytes above: it hashes
the normalized pool/arrangement/line data, not the serialization.

The recorded seed and successful step belong to the producer's search
provenance. I verified the finite certificate directly; I did not rerun all
154528 search steps and do not claim such a replay. The exact verification
establishes the next-order repair without relying on the search heuristic.
The manuscript correctly limits that positive order-four assertion to K9.
It does not infer an order-four theorem for all powers of three, and it does
not change CYC's sufficiently-large-tail statement or any canonical pool.

Commands actually run from the repository root:

```sh
python -B problems/cyclotomic-prime-arrays/code/generate_ternary_cube_obstruction.py /tmp/ternary-review-cube3-unsat.json
python -B problems/cyclotomic-prime-arrays/code/replay_ternary_cube_tree.py --negative-controls problems/cyclotomic-prime-arrays/inputs/ternary_cube3_unsat.json
python -B problems/cyclotomic-prime-arrays/code/check_ternary_cube_obstruction.py --negative-controls --independent-search problems/cyclotomic-prime-arrays/inputs/ternary_cube3_unsat.json
python -B problems/cyclotomic-prime-arrays/code/check_energy_certificate.py --negative-controls problems/cyclotomic-prime-arrays/inputs/energy_m9_cube4.json
```

**Review conclusion:** no blocking mathematical or implementation issue was
found in the stated nonauthor scope at the exact supplemental source.
The order-three impossibility is proved by the local arithmetic and explicit
finite certificate; the K9 order-four existence is proved by its exact array
certificate. The review makes no independent acceptance claim for its author's
earlier energy checker and no claim of kernel verification or external review.
