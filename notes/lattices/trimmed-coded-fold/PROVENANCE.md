# Provenance, attribution, and verification

## What is published

This is a selected mathematical release from `Mira-Cult/cvp`, draft PR 369,
commit `1a2a2b06e1942e6938ccb8b51a33deb43f0380bb`, titled
“[CVP-M10] Trimmed coded folding: smaller rank and explicit overhead.”
It was open and marked draft when inspected on 26 October 2026. Publication
of this note does not merge that PR or change the upstream accepted status.

The new README is an AI-assisted exposition of that packet. The five files
under `proofs/` and six scripts under `experiments/` are exact selected source
copies, not an entire private checkout. `SOURCE_PINS.json` records the source
path, immutable commit, Git blob identity, and SHA-256 of each copy. The
source paths `docs/NAME.md` correspond here to `proofs/NAME.md`. No private
conversation or user attachment is included.

The research and proof packet are attributed to the Mira-Cult CVP project.
The upstream packet records model-assisted authorship and reviews, including
separate audits of the code, finite Hankel theorem, compiler and schedule.
These are not human expert endorsements. No priority claim is made for the
general Hankel theorem or other antecedent algebraic methods. The independent
external paper is by Giacomo Fenzi and Guy Weissenberg; its claims are
attributed and linked in the note, not incorporated as our own theorem.

No repository-wide license has been selected. Public availability is not an
additional license grant, and this release does not relicense third-party
work. Attribution and any applicable rights in antecedent work are preserved.

## Historical references in the frozen copies

The copies retain original prose and backtick references so that hashes
remain meaningful. References to `CODED_FOLD_UNIFORM_SCHEDULE.md`,
`PACKED_TWO_LEVEL_FOLD.md`, `SYMMETRIC_MULTILINEAR_FOLDED_ATOMIZER.md`, older
paper modules and reconstruction-obstruction notes describe historical or
alternative results. They are **not additional premises** of this release's
trimmed theorem. The current schedule is `TRIMMED_FOLD_PARAMETERS.md`.
The five local proof files give the complete applicable dependency chain;
the README's Section 8 links their relevant sections.

References to original `reviews/` describe the upstream review record,
which is not copied wholesale. In particular, frozen SHA-256 values recorded
by the trimmed compiler audit agree with these source files:

- `TRIMMED_CODED_FOLD.md`: `c81c4c38cc5268a1f9127ec3e7a395b53919c423df6acac8667255741c68b357`
- `CODED_PACKED_TWO_LEVEL_FOLD.md`: `380bb8d860c6458c1ecbc4ab7d3d9bbb68c8343e58e55388908929407950e374`
- `CODED_CHANNELS_LEMMA.md`: `d17d7cd4df4278afc9cfd0d04e75c3ace44fbca7f9471fcc8cd7de882099f1c8`
- `VECTOR_HANKEL_ATOMICITY.md`: `60900f1f320728c1347449440b6fb353cac3280d17a9a45e1b19ae074a66a91f`

## Reproducible finite checks

Python 3 and its standard library suffice. Run from this note's directory:

```sh
python3 experiments/check_trimmed_sampling.py --output /tmp/trimmed_sampling.json
python3 experiments/check_trimmed_fold_parameters.py --output /tmp/trimmed_parameters.json
python3 experiments/vector_hankel_atomicity_check.py --output /tmp/vector_atomicity.json
python3 experiments/check_coded_channels.py --output /tmp/coded_channels.json
```

The two other scripts supply imported finite-field and predecessor-schedule
routines. Generated JSON outputs are not required source files and are not
included. None of these scripts instantiates the full asymptotic compiler.
The parameter examples with enormous $`L`$ use virtual $`N=2^L`$, not enormous
materialized fields or lattices.

Release preparation reran all four checks successfully:

- Subset sampling: 1,097,728 rank inequalities; output SHA-256
  `cfa120550c8c2b9916486b8e9515bfe235eb4b8a34cda43bb1104a765bac8e29`.
- Parameter schedule: 1,128 direct integer comparisons, 1,295 exhaustive
  versus binary searches, 191,345 monotonic-margin steps, 345 field/rank/gap
  cases, 90 saving checks, 18 cutoff cases; output SHA-256
  `2b0284691b8e235177be8994e68c48efe44d4055a2b7da8d81a385da3a974e6a`.
- Coded channels: 8,190 code messages, 4,416 local tables, 265 schedules,
  and 32,000 signed integer residual checks; output SHA-256
  `11cf23c1f123deb84c58f657d7856f90bedc150ed899971fd18ed573374759dc`.
- Finite Hankel extraction: binary vector and matrix exhaustions, an
  extension-field scalar family, characteristic-polynomial identities,
  a boundary spike, and rejection of a repeated-root counterexample.

Source content was checked against pinned Git blob identities. Focused
mathematical reading checked the two-level determinant charge, finite
Hankel prefix, coefficientwise decoding, parity identity, exact strict
parameter predicate and asymptotic balance. A separate model-assisted
reader found no blocking issue in that dependency chain. These activities
are neither formal verification nor external human review. They do not
establish a tested end-to-end implementation, and finite tests alone do
not establish the general theorem.

## External comparison source pin

The comparison was checked against the 25 October 2026 PDF of
*Nearly Optimal Hardness for CVP and NCP with Preprocessing*, by Giacomo
Fenzi and Guy Weissenberg, ePrint 2026/2634. PDF SHA-256:
`e59ecf6e91e4254e0abf4c1e9ff1cbca1a9801f9df394429d3b0bc397c0fdbde`.
The resource estimate is Appendix A.4, pp. 40–41, equation (37) and its
following inequality; the lattice conversion and strict gap choice are
Theorem 5.1, pp. 26–27. The PDF is cited, not redistributed.
