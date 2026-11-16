# Release audit: 15 November 2026

## Source and export

The selected research snapshot is commit
`27d51e6a23363d6c0ae74b2f6f752db9bb5e5847` of Mira-Cult/math-wip, problem 0323.
That private source is provenance, **not a required public proof link**. The
selected source files are reproduced in [the packet](packet/README.md), with
[original and exported hashes](packet/MANIFEST.json). The packet contains 47
upstream files and one newly written independent arithmetic checker.

The export retains mathematical text and review-source revisions. Internal
reviewer thread identifiers were replaced with explicit omission labels.
Links to omitted contextual claim/index pages and unrelated continuations were
rendered as labeled text. These omissions are enumerated in the manifest; they
must not be treated as supplied or independently audited proofs. Existing
third-party references remain citations, not copied full papers.

## Mathematical review boundaries

The rigid-center example received a new scoped nonauthor model audit of its
construction, transversality, strict-defect simplicity argument, properness,
principal isotope, isomorphism obstruction, and no-Bruck-isotope deduction,
including the specified used interfaces. No defect was found in that scope.

The other selected constructions received review of their local proof arguments
and dependency identification. This is **not** a new complete review of all
supporting classification theorems. In particular, the whole class-two exhaustion
theorem and global Bol classification are not certified by this release.
Historical model reviews in source manuscripts retain their historical scopes.

No human expert refereeing, kernel-checked formalization, complete huge-loop
enumeration, or literature priority certification is claimed.

## Reproduction performed for this release

From `packet/`:

```sh
python3 code/verify_odd_rigid_center.py
python3 code/independent_bch_section_check.py
python3 code/verify_odd_heisenberg_jacobi_obstruction.py
```

All three completed successfully. The first returned direct Moufang central
values 12 and 18. The second checked 10,000 independently calculated fixed-seed
BCH-section products. The third verified the q=2311 primitive-root and
Jacobi-square obstruction for its specified construction support.

All included Python files passed syntax parsing. All relative Markdown file
targets exist in the staged export; this does not validate every external URL
or automatically check all heading anchors. All 48 packet manifest file hashes
matched. Other included scripts were not rerun in this release audit unless an
individual report explicitly says so.

The export was scanned for credentials, internal reviewer identifiers, private
conversation links, local personal paths, and unrelated speculative material.
It changes no source-repository permissions and does not disclose the entire
private research workspace.
