# Validation and evidence limits

## Release checks (2026-11-01)

Checked locally with Python 3.12.14, using only the Python standard library.
Run commands from this directory; outputs go outside the repository.

| Command | Result and exact scope |
| --- | --- |
| `python code/verify_v3.py` | Passed. Rebuilds the literal source and polygons, checks all selection hashes, all 30 displayed tuples, 420 genuine sides, the observer bytes, exact local contact certificate, and periodic core coverage. |
| `python -m unittest discover -s code -p 'test_*v3.py' -v` | Passed: 37 tests, including arithmetic, both source frames, geometry, malformed certificates, and recurrence adversaries. |
| `python code/build_v3.py --candidate parity30-profile14 --out /tmp/collatz30` | Passed. Produces the selected exact 30-shape JSON, source alphabet, contact certificate and summary without Collatz search. |
| `python code/verify_v3_cells.py --certificate /tmp/collatz30/parity30-profile14-contact-certificate.json` | Passed. Separate exact ray-crossing/unit-cell audit: 6,651 overlap witnesses, 744 cavity witnesses, 49,706 closed cavity-boundary edges. |
| `sha256sum -c SHA256SUMS` | Checks public file integrity; it does not prove mathematics. |

The selected generator output is 10,156 bytes, with SHA-256
`a417e7ac065bdba092d334fce5dfe27821da15f74aa23f5f4ed4b3b7107a2d17`.
The exact contact-certificate SHA-256 is
`b32b6d91733d571f1dcef2a6b5eef9c03232275f331f30c8e1d49cc7c2120aa0`.
The observer is 1,092 UTF-8 bytes with SHA-256
`8a7c4482c2536cfaa78c60f2918e466e3d3dd2fa1671990d2fe6e9707af21824`.
These match the source scientific freeze and the selected poster construction.

## What is proved and what is checked

The geometry manuscript supplies the arbitrary-placement/global-plane argument.
Finite exhaustive checks discharge its explicitly finite corner/contact cases;
they are not a bounded-search inference that all infinite tilings behave well.
The arithmetic and frame manuscripts prove both directions of the infinite
recurrence equivalence, including initialization, whole-plane completion,
coverage of every positive odd target and exclusion of nonstandard accepted
streams. Neither finite tests nor the poster establish infinite recurrence.

The finite adversary tests include missing or invalid geometric witnesses,
counterfeit event contexts, quiet/rootless alternatives and nonstandard runs.
They supplement, not replace, the proofs. No formal proof-assistant certificate
or external human expert review is claimed. A separately implemented finite
checker and internal task-agent reviews are not a substitute for either.

## Public-source adaptations

Scientific code, the three selected inputs, and the supporting arithmetic,
frame and geometry manuscripts are preserved byte-for-byte from the pinned
scientific source. The main theorem and problem statement have only
public-facing reference/scope edits: private review/evidence links were replaced
with this guide, and historical variant/project-maintenance discussion was
removed. Their mathematical statement, tuple table and proof are unchanged.
[SOURCE.json](SOURCE.json) records original and public hashes per file.
The README, attribution, this guide and release manifests were prepared for
this publication. Private discussions, work orders, review transcripts and
unselected historical variants are not part of the public packet.
