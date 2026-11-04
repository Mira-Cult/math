# Attribution and license status

## This machine and its formalization

The selected 285-state construction, its compression work, and the Lean
formalization are Mira-Cult research artifacts. The original producer revision
is `db256d6ae59a47eb941a2f0c5cf3f37b3c4633c8`; the formalization revision is
`d2352cd63de5840d05dcdc89e78dc9f7052ee32f`. Exact paths and hashes are recorded in
[PROVENANCE.json](PROVENANCE.json) and [SOURCE-MANIFEST.json](SOURCE-MANIFEST.json).
Those historical identifiers are provenance, not dependencies on access to a
private repository. The required source and literal data are included here.

The 285-state producer follows a 290-state construction, an operation-specific
operand-dispatch change, and five contextual zero-operation eliminations.
Its marked-transition table and its 286-state B-exit companion are distinct
artifacts. Earlier internal source/control and physical reviews concerned
that construction and compression; they are not reviews of the later Lean
formalization. This release does not relabel those reviews as external or
human certification. Later source/interface review was performed by the user's
assistant with separate nonauthor automated reviewers, not by Mira personally.
The exact scope and revisions are in [VERIFICATION.md](VERIFICATION.md).

## Formal infrastructure

The formal proof uses [Lean 4](https://github.com/leanprover/lean4),
[mathlib](https://github.com/leanprover-community/mathlib4), and
[Google DeepMind's formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
The pinned `ComplexityTheory.P` and `ComplexityTheory.NP` definitions come from
formal-conjectures; the machine and computability framework imports mathlib.
The lockfile preserves all ten direct and transitive package pins. These
dependencies retain their upstream copyrights, authorship, and licenses.
The local `Shared` sources retain their original headers unchanged.

The source architecture has a broader history involving finite-model Horn
search, but the endpoint released here uses the explicitly clocked program
reference and canonical complexity bridge described in [PROOF.md](PROOF.md).
It does not invoke an unstated Horn capture theorem as a premise.

## License choice

No new repository-wide or package-wide license is granted by this publication.
Public availability is not a relicensing of this project or of any dependency.
An additional license choice remains with the rights holders.
