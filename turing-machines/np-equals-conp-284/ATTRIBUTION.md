# Attribution and license status

The selected construction, compression work and Lean formalization are
Mira-Cult research artifacts. The 284-state table producer is
`7b90875183aa928fb19a4a9bf333b8ced2194ded`; the mathematical formalization
revision selected here is `6108c93565701e64775a3f1cbf9627d35c4c30e3`.
Exact file identities belong to the accompanying source manifest.

The result uses the standard search pattern that turns an existential claim
about an everywhere-correct candidate into finite beeping. The concrete
contribution is the complete small binary machine and its paid source-to-tape
and canonical-complexity arguments. It does not settle NP versus coNP.

The formal proof uses [Lean 4](https://github.com/leanprover/lean4),
[mathlib](https://github.com/leanprover-community/mathlib4), and
[Google DeepMind's formal-conjectures](https://github.com/google-deepmind/formal-conjectures).
The pinned `ComplexityTheory.NP` and `ComplexityTheory.coNP` definitions come
from formal-conjectures. The framework uses mathlib's computability and
complexity machinery. Dependencies retain their upstream copyrights,
authorship and licenses.

Kernel checking, internal nonauthor automated source review, and public-packet
finite checks are separately described in [VERIFICATION.md](VERIFICATION.md).
No review is attributed to Mira personally or represented as external
human-expert certification.

No new repository-wide or package-wide license is granted by this publication.
Public availability is not a relicensing of this project or its dependencies.
An additional license choice remains with the rights holders.
