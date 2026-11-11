# Scoped prepublication review

Date: 11 November 2026. Review performed separately from the authoring pass.

## Verdict and exact scope

No unresolved correctness defect was found in the reviewed core arguments of `MANUSCRIPT.md`: Theorem A, Lemma B, Corollary C, Theorem D, Corollary H, and Appendices A–B. These are suitable for release as a clearly labeled mathematical research manuscript with the stated external dependency and review limitations. This verdict is not external expert/referee acceptance, formal verification, a historical-priority determination, or a promotion of any predecessor's audit status.

The elementary arguments in `TRANSFER_AND_OBSTRUCTIONS.md` were read and checked at their stated scope. The singular, flat, and near-polynomial arguments in `EXTENSIONS.md` received targeted checks of their principal estimates, rather than the same complete core review. They remain separately labeled producer-proof drafts. No conclusion about later Gaussian, splicing, fractional-schedule, or joint-operation manuscripts is included.

Reviewed file bytes (SHA-256):

- `MANUSCRIPT.md`: `3a339b86b82966da6593280d7aa9d2aabd1223c099b3bb92c90b1eaf35b828da`
- `EXTENSIONS.md`: `0f269bd257092021b6e938ac9024c0a9dde6060a9dfca02c464b82cf9f4c2610`
- `TRANSFER_AND_OBSTRUCTIONS.md`: `f2b07d51bfd69d27d0888de367213238fd1a1129c86e47b6ce1767e12d249862`
- `verify_finite.py`: `798321eb977c24f2c6e4078444c3b562fbc8b4c99f461c8845ea9de1fcd552d4`

Hashes authenticate the reviewed versions, not the truth of their mathematics. Subsequent mathematical edits require renewed review.

## Core checks

- The coefficient upper bound and finite-window lower bound give a dominant derivative on the entire real sampling interval. Individual zero coefficients are allowed; an entire zero window is not.
- The backwards companion-matrix estimate yields the stated factorial-scale window lower bound. The D-finite reduction removes identically zero endpoint polynomials, passes their finitely many roots, and preserves the distinction between existential and effectively supplied constants.
- The source schedule uses only the common positive radius, base and chosen budgets. Constants and onset may depend on the window data. A common schedule is not confused with a uniform estimate over a degenerating family.
- The three exponents in the absolute derivative estimate are nonnegative functions of interval length. Replacing a partial row interval's length by the full stage length is therefore justified; very short intervals are handled trivially.
- The Fourier cutoff depends on the actual digit offset. Geometric summation, crossing words, an unfinished row and the whole preceding stage account for every output prefix. The bounded-increment depth condition is used in the preceding-stage lower bound.
- The two regular-power recurrence formulas and their exact integer-polynomial exceptions are correct. Their failure proof concerns those rational/integer polynomial endpoints, not arbitrary real-coefficient polynomials with a potentially normal additive constant.
- Corollary H correctly states a center-uniform dichotomy. In its negative direction, clearing rational polynomial coefficients places deep phases on a fixed finite grid, so one sufficiently long canonical radix cylinder is absent.
- The Fejér majorant/minorant argument includes endpoints and gives the stated elementary Fourier-to-word inequality.

The imported analytic contract was checked against Juan Arias de Reyna, arXiv:2407.02094v1, Theorem 11 (15) and Remark 14 (19). Its actual constants are below 11 and its derivative-order, interval-length and sign hypotheses match Appendix A's weaker constant-12 formulation. The external paper's full proof was not independently reproved in this review.

## Companion and extension checks

The shifted-orbit transfer retains the essential factor `b^(S_(j-1))`; mere unshifted source convergence does not suffice. The logarithmic grid retains the base-supported denominator factors. The source-count obstruction requires uniformity over additive centers. The local inverse approximation and repeated-packet Liouville arguments have their stated scope.

Targeted extension checks covered the singular floor inequality, the Bell/Lah remainder estimate, the derivative margins for the two flat examples, and the near-exception proof's retained epsilon factor. The latter uses the entire preceding stage and a long constant word, including the negative-parameter borrow, rather than an unjustified single-digit excess. No compact-uniform singular theorem across positive integers is inferred.

## Corrections made before this verdict

- Replaced ceilings of transcendental logarithmic expressions in the flat schedules by exact integer threshold schedules with the same asymptotic bounds. Optional root-growth examples likewise use integer data.
- Included the full derivative-estimate contract and Fejér proof instead of inaccessible local references.
- Restated missing notation and integer domains, removed the stale balanced-schedule pointer, and made the rational-derivative necessity explicitly center-uniform.
- Rephrased the normality/transcendence statement as an unproved implication, not as a known counterexample.

## Independent finite replay and limitations

Fresh executions of `python3 -B verify_finite.py`, `python3 -B -O verify_finite.py`, and `python3 -B -OO verify_finite.py` all passed 1,332 finite cases and produced byte-identical JSON output. The public checker is byte-identical to the recovered source checker. Its checks cover recurrence identities, finite coefficient windows, algebraic digits, carries, inverse identities, offset geometry and Bell majorants. These finite checks do not certify asymptotic normality or the new schedule formulas.

The primary-paper comparisons in `REFERENCES.md` were checked at the named statements: Becher–Heiber–Slaman already construct a computable absolutely normal Liouville number; Madritsch–Thuswaldner–Tichy treat integer-part concatenations for logarithmic order strictly between 1 and 4/3. The latter is a different observation model from shrinking-input fractional prefixes. The targeted search does not establish novelty. A deeper literature review and external mathematical review remain appropriate before a journal submission.
