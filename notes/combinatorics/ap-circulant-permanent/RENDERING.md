# GitHub rendering verification

Date: 2026-11-08.

The actual GitHub preview was inspected at candidate commit
[`3802e1de100e9f727b34122775796154ddedffdc`](https://github.com/Mira-Cult/math/commit/3802e1de100e9f727b34122775796154ddedffdc).
The final source files retain those exact bytes.

- `README.md`: 144 inline expressions and 14 display expressions, all 158
  represented by rendered MathML, with no rendering errors or unrendered
  expressions.
- `PRIOR_ART.md`: 78 inline expressions and five display expressions, all
  83 represented by rendered MathML, with no rendering errors or unrendered
  expressions.
- Both direct-recurrence displays have three aligned rows. The terminal
  sum has both constraints in its lower limit. The full index range,
  staircase indicator, gadget edge conditions, and balance equations were
  checked in the rendered output. Screenshots of the note, recurrence, and
  appendix were visually inspected.

The first preview exposed GitHub's consumption of literal angle brackets in
some fenced math expressions. Before advancing the main branch, the source
was changed to use the equivalent TeX operators `\lt` and `\gt` inside math.
No algorithm, theorem, proof, example, or complexity claim changed.

## Relationship to the mathematical review

[INDEPENDENT_REVIEW.md](INDEPENDENT_REVIEW.md) preserves fingerprints of the
reviewed pre-rendering source at commit
[`8c435024a91248c1e8185dff90895bb0b70639eb`](https://github.com/Mira-Cult/math/commit/8c435024a91248c1e8185dff90895bb0b70639eb).
For both changed files, replacing `\lt ` with `<` and `\gt ` with `>` in the
final source reproduces the reviewed source **byte for byte**. This exact
equivalence was checked against the saved publication inputs. All other
reviewed files, including the implementation and tests, are unchanged.

This rendering addendum is publication verification, not a second
mathematical review. The review's scope and limitations remain as stated in
its report.

Final source SHA-256 fingerprints:

```text
19e2fdc80cd54ffc4ca971903e4c79cc0cfbfc9c8712d6881ef14b320a52af4d  README.md
8a0516d98ac360eb656b4a4837aa8945677864d5860c94c59815406a2ecd7b4b  PRIOR_ART.md
```

The checked rendering is GitHub's desktop web preview. Different clients may
apply different typography. The math source, proof, code, and tests are
available independently of that presentation.
