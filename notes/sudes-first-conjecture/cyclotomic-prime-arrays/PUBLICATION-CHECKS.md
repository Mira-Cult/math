# Publication validation

Publication replay: 3 November 2026, Python 3.12.14, standard library only.
This file distinguishes checks rerun for this public package from historical
review observations. No end-to-end formal proof or external referee acceptance
is claimed.

## Fresh successful replays

- Eight energy-model arrays verified, including all 76 lines of the K9 order-four cube; 116 corrupted certificates rejected.
- Nine frozen quartic arrays verified; 90 mutations rejected.
- Ternary obstruction proof tree verified: 31 nodes, 15 branches, 16 conflicts, 220 forced assignments. Eight mutations rejected and a separate exhaustive search returned unsatisfiable. The author's separate tree replay also passed and rejected its two controls.
- Integer tensor correction: 192 exact corrections across orders 3–18; four negative controls rejected.
- Three physical quartic fixtures: each has 729 entries and 301 lines; all 16 orientations checked per field, with ten rejected mutations per fixture. These are physical trade fixtures, not all-prime arrays.
- Local ledger: 21 prefixes, 49 residue histograms, six order-two obstruction witnesses; five mutations rejected.
- Exact unit subgroup certificates regenerated and matched the distributed JSON byte-for-byte. Independence is certified, not index one in the full unit group.

The code and input bytes are identical to the pinned delivery. Reproduction
commands are in the main README. Finite controls test bounded instances and
interfaces; the eventual theorem requires the complete conventional proofs
and named external analytic imports.

## Source and publication boundary

The source map records SHA-256 hashes for every source file and reading copy.
Original Markdown is archived unchanged. Editorial reading copies adapt math
delimiters and public links, not mathematical statements. The inherited square,
cube and quadratic geometric dependencies have public reading copies with
scientific source pins; the README links each dependency explicitly.

This publication does not run the private research repository's fleet workflow
or claim its skipped workflow was a pass. No repository integration/merge or
formal PR approval is part of this mathematical publication.

## Anonymous publication checks

At public commit `9dab1ce77eb2984a28749bb8dc440e02e562aa7d`, all 86 package files were downloaded anonymously from GitHub and matched the staged bytes exactly. The main README and four general proof manuscripts were fetched as GitHub-rendered HTML: the README, analytic proof and controller contained rendered math elements with no reported math parse errors; normalization and composition use prose/code notation. A full browser screenshot was not obtained because Chromium could not launch in this execution environment. This is HTML/render-markup verification, not a visual screenshot review.
