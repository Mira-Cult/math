# Initial paper PDF review

Reviewed 11 November 2026. This companion records the initial readable paper, not the later expanded collection. It is deliberately separate from the mathematical paper.

The reviewed artifact is `paper/normal-dovetails.pdf`, 30 pages, with source `paper/normal-dovetails.tex`.

- PDF SHA256: `b14c662c944dbf8d3b2246a92a584acf79073d096f7d883c5a1ff4433f4901f0`.
- TeX SHA256: `47ebf5ebefcc97ea12fae87f7aed2c31849cef6e5812977507d74a14722a611b`.

## Coverage and outcome

Every rendered page was visually inspected after conversion to PNG, including all long derivative, Bell-polynomial and resource estimates. No clipped formulas, overlapping text, missing glyphs, unresolved references or visible literal-dollar/math-delimiter defects were found. The PDF has consistent page numbers and a working table of contents. Its only external link annotations are the three mathematical bibliography URLs. A broken relative proof-appendix link from the preceding 29-page build was removed before this review.

The paper contains Sections 1–8 and Appendices A–C. Theorem labels A–H retain their mathematical meanings. The elementary companion is incorporated as Propositions C.1–C.10, with equations formerly tagged 7.x changed to C.x; the local references were updated. The source conversion was checked against the reviewed mathematical material, including the selected-order restriction in the near-polynomial estimate. Explanatory introduction, notation definitions and open questions were added without strengthening claims.

The initial conversion's display-math parsing defect was caught and corrected before the PDF was built. A source comparison and rendered inspection confirmed the repaired display formulas. PDF text extraction maps two large floor-delimiter glyphs to dollar characters; these are visibly correct floor signs in the PDF, not literal dollar signs or broken mathematics.

There are no hashes, Lean-source references, audit badges or low-level verification discussion in the paper. These remain in separate companions.

## Limitations

The complete conventional proof audits for Sections 1–7 and the elementary appendix are recorded in `CORE_AND_COMPANION_AUDIT.md` and `EXTENSION_AUDIT.md`. The resource proofs have their own scoped review in `resource-proofs/REVIEW.md`. This PDF itself presents the signed-mixture extension and balanced resource estimate as a proof sketch or proof outline; the complete technical arguments still need incorporation into the final self-contained expanded paper.

This initial PDF does not yet contain the subsequently recovered historical logarithm, joint-operation, schedule, Gaussian or selected-source results. Their separate review and final source-to-PDF checks are not certified by this note. No external referee acceptance, formal verification, exhaustive literature-priority conclusion or announcement-readiness of the entire corpus is asserted.
