# Verification and review limits

Prepared 11 November 2026.

## Mathematical review

[REVIEW.md](REVIEW.md) records a fresh nonauthor model review, its actual scope, findings, fixes, and SHA-256 fingerprints of the mathematical files. The reviewer did not write those arguments or perform a formal GitHub approval. This is scoped automated mathematical review, not an external human expert/referee report and not a formal proof.

The main coefficient-window argument, recurrence lemma, D-finite reduction, regular-power exceptions, rational-derivative dichotomy, and elementary companion proofs were read at their stated scopes. The singular/flat/near-exception material remains labeled as producer-proof drafts with the review qualifications recorded separately. Neither a source merge nor a finite checker certifies every analytic statement.

The primary Arias de Reyna theorem was checked for the exact order, interval, sign, and constant hypotheses used here. This is a statement-and-application check, not an independent reproving of its deep analytic estimate. The recent draft composition/splicing/fractional/Gaussian branches and the whole older gist corpus are outside this release's mathematical review.

## Exact finite replay

The unchanged generalized-centers checker, publicly named `verify_finite.py`, was run with Python 3.12.14 in each of these modes:

```sh
python3 -B verify_finite.py
python3 -B -O verify_finite.py
python3 -B -OO verify_finite.py
```

All three executions exited successfully with the same complete JSON result. The independent reviewer separately reproduced the same output. There were **1,332 finite cases**:

- 828 regular-power recurrence cases;
- 231 inverse/polynomial identities;
- 100 cosine-window cases;
- 64 reciprocal-square Bell cases;
- 37 algebraic-digit/borrow cases;
- 20 nonconstant-exception borrow cases;
- 20 offset-geometry cases;
- 20 corrected singular-floor cases;
- 12 flat Bell-leading cases.

Assertions remain effective under optimization. No finite digit-frequency experiment is offered as evidence of normality. The new integer-threshold schedule transcription is justified by exact comparisons and the proof's asymptotic estimates, not by this unchanged historical checker.

## Packaging and reproducibility

The release contains readable proof source, references, provenance, review metadata and one standard-library Python checker. Local relative Markdown links and reviewed source fingerprints were checked before publication. The two recovered public historical archives matched their recorded byte counts and full-file SHA-256 hashes. No generated PDF, build cache, raw execution log, or copied private status dump is part of the source release.

To reproduce the finite evidence, run the commands above. To inspect the infinite theorem, read the manuscript and its explicit analytic dependency. These are different tasks.

## Claims not made

- No formal or proof-assistant verification of the infinite theorem.
- No complete independent rebuild of historical companion projects.
- No external expert/referee acceptance or journal submission.
- No historical-priority or universal-optimality claim.
- No normality result for an unchanged traditional constant.
- No upgrade of the separate active draft research lines.
