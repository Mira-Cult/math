# Source provenance and editorial changes

This public release was prepared from mathematical source files, not from private conversations. No credentials, generated build products, active-lane state, or unrelated research were imported. Publication does not change source-branch ownership or audit status.

## Principal proof

- Source project: Mira-Cult/normality-research.
- Snapshot inspected: `dd64aa38f4321953c5695eaefe381ab9624649b3`.
- Corrected generalized-centers source commit: `ee4c66e407bc5477d1172f1ca0255ead663464a0`.
- Original file: `research/generalized-centers-20261019/PAPER.md`.
- Original UTF-8 size: 45,000 bytes.
- Original SHA-256: `acade6b34ef0d6f6089fd13ff4860287fea1fab77976002be2e87435d0a7b1f1`.
- Original finite checker SHA-256: `798321eb977c24f2c6e4078444c3b562fbc8b4c99f461c8845ea9de1fcd552d4`; the public `verify_finite.py` preserves these bytes unchanged.

The source recorded scoped maintainer review on 20 October 2026 and a pending external audit. This release keeps that distinction. Its fresh review is recorded separately in [REVIEW.md](REVIEW.md).

The public manuscript preserves the central coefficient-window, recurrence, D-finite and regular-power arguments, adding an accessible introduction and explicit analytic/Fourier appendices. Those appendices come from the same snapshot's `docs/research-notes/multiscale-fourier-20261019/derivative-proof.md` §1 and `docs/research-notes/multiscale-fourier-batches-20261019.md` §8. The short rational-derivative dichotomy is rederived directly from the main theorem and the polynomial finite-grid obstruction, rather than importing unreviewed resource bounds.

## Explicit successor corrections

The public text is an edited successor, not a byte-identical republication of PAPER.md.

1. Private navigation, lane instructions and integration history were removed from the mathematical exposition. The essential source identifiers and actual review limits remain here.
2. The growing-order derivative contract and the endpoint-safe Fejér proof are reproduced explicitly, replacing otherwise inaccessible local references.
3. Flat-kernel schedules previously written using ceilings of transcendental logarithmic expressions now use exact integer threshold tests. For the reciprocal kernel, $B_r=3+\min\lbrace m\ge1:b^{b^m}\ge r+4\rbrace$; for reciprocal-square, $B_r=3+\min\lbrace m\ge1:b^{b^{2m}}\ge r+4\rbrace$. These preserve the stated asymptotic comparisons and make computability immediate.
4. The optional cube-root and square-root growth examples in the main theorem use integer roots of the binary bit-length of $r+2$, preserving their stated asymptotic orders.
5. The old extraction's notation for circle distance, integer offsets and nonnegative guard exponents is restated. Statements about transcendence are phrased as proof limitations, not as a purported counterexample to the open normality/transcendence implication.

## Older elementary companion

`TRANSFER_AND_OBSTRUCTIONS.md` adapts the average-orbit-distance, shifted-shadowing, logarithmic grid, source-count, initial-zero, analytic-rigidity, inverse-approximation and normal Liouville proofs in `manuscripts/theory-of-normality/chapters/07-constructions-and-barriers.md` from the same inspected snapshot. Its historical labels CON-002–009 and BND-001–003 are retained as locators. It omits the stronger historical producer claims that this release did not reconstruct.

## Public historical archives

- Earlier gist revision: `d699a69c2037ee4420bfb8e1e0ad0b310bbc8eb0`. Full original SHA-256 `be2dcfbc9e60f8b2611149ecc035cfe283588cb45ee2662930d6c27b2d0ba3db`, 529,786 UTF-8 bytes. Physical LF line counting matters: the original has an unterminated final line and a literal form feed inside an old TeX fragment.
- October 7 gist revision: `41b5a780f79f7bdd275cd96e7e310b000a897d35`. Full original SHA-256 `d66fd02277f19f2189b3ccf068a208e938a30832bb6d40a2a376b6bd3875c26f`, 594,769 UTF-8 bytes.

Both originals were recovered and their full-file hashes checked during preparation. They are already public at the revision-specific links in [REFERENCES.md](REFERENCES.md). Their full contents are not silently certified by this release's scoped review.

## Excluded recent drafts

The November 11 inventory identified additional draft branches for Gaussian constructions, position-aligned splicing, fractional schedules and joint-operation certificates. Their mathematics was not merged, rewritten or promoted by this public release. The history page records their place in the program without using inaccessible draft claims as proofs of anything here.

## Attribution and licensing

These are Mira-Cult research sources with external mathematical dependencies credited in the references. No new license or transfer of third-party rights is declared by this release. Earlier sources retain their own attribution and terms.

## Unified notation edition

The rendering revision combines the former main and extension files into one manuscript, states the coefficient-window theorem first, and uses GitHub-supported TeX notation throughout. Mathematical review scope remains section-specific. The singular, flat, and near-polynomial arguments are not promoted by moving them into the same file. The separate `EXTENSIONS.md` file is removed only after its full content is incorporated.

Result labels in the unified edition are: A (window theorem), B (recurrence lemma), C (D-finite corollary), D (rational-derivative dichotomy), E (regular powers), F (singular powers), G (flat sources), H (near-polynomial scale). The initial edition used D for regular powers, H for rational derivatives, and E/F/G for the last three results. The equations are renumbered to match their sections. No endpoint, estimate, or parameter range is enlarged by this reorganization.
