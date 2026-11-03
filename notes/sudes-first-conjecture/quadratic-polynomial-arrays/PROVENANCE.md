# Source provenance and public proof closure

Publication date: 3 November 2026. This is a conventional, internally reviewed mathematical theorem, not an end-to-end kernel-checked result or external referee endorsement.

## Frozen scientific revisions

- New quadratic argument and producer: scientific revision `e0cf4e8808f21c0633326f70f42a870086836320`, recovered from final reviewed delivery `a05039dc21d48e90414f8a4a80875405c9760e69` (research PR86). Their hashes agree exactly with the independent review.
- Baseline characteristic-zero estimates and permutation bridge: `3ea1a0389c2165a71d5abedf6b4c036f8b9f0166` (research PR84).
- Original independent review and reviewer oracle: final reviewed delivery `a05039dc21d48e90414f8a4a80875405c9760e69`.

These identifiers record scientific provenance. All files needed for the quadratic proof and replay are included here, so neither access to the research repository nor its Git history is required.

## Dependency map

1. [Public theorem](README.md) fixes the canonical coefficient order and full signed-line geometry.
2. [Improved proof](sources/transfer.md), PQ1 and §§1–6, proves the new bounds. It imports the baseline height count and sampling arguments, not the baseline's much larger cutoff.
3. [Baseline proof](sources/characteristic_zero.md), Lemma 1.1, pairing construction and Lemma 3.2, supplies those elementary arguments in full.
4. [Permutation bridge](sources/permutation_bridge.md), Theorem PL, supplies both conflict budgets and the local-lemma composition.
5. [External import list](REFERENCES.md) names the precise Lu–Székely and Gauss-lemma results. No prime-pattern hypothesis is needed.
6. [Independent review](sources/review.md) records the mathematical and implementation audit. It is an edited presentation of the original review: execution-environment paths and unrelated finite-field proof sections are omitted. The author and reviewer were distinct.
7. [Replay guide](code/README.md) gives all commands. The independently implemented reviewer output was regenerated and matches SHA-256 `6749fe80de7a90d39c98aecefc513e5b900ce0a107ac62473996a441bc96e949`. The producer's exact controls also passed.

The browsable proof copies normalize GitHub math formatting and local links. The improved-proof copy omits the separate finite-field sections. Exact original proof and code bytes remain in `originals/`; their hashes below distinguish presentation edits from scientific changes. The public reviewer adapter changes source loading only, checking the original manuscript and producer hashes before executing the source. Its comparisons are unchanged.

## Exact original-file SHA-256 values

| File | SHA-256 |
|---|---|
| [originals/characteristic_zero.md](originals/characteristic_zero.md) | `3865e5685c515261eb3426fc6c2d42795b68203f8a2b2264c6d13c2074140604` |
| [originals/permutation_bridge.md](originals/permutation_bridge.md) | `3eb52979c6a822f34a784180f18eca1e316c19eaba782671e1bdbaa57be323b3` |
| [originals/polynomial_bound_transfer.py](originals/polynomial_bound_transfer.py) | `a055792d25dc13567b15aa14eaab454b66eef100b22199c70f74cacbdc647e3c` |
| [originals/polynomial_transfer_independent_oracle.py](originals/polynomial_transfer_independent_oracle.py) | `3f48ef9f0f7981b9854c0a6dd3e54f55185a7ca85ef19b9b86a0fb1cbb88702d` |
| [originals/transfer.md](originals/transfer.md) | `269829f323333396a8b6abd9db422bf142f7d3c869a0789c1eba2d0f94d5d739` |
