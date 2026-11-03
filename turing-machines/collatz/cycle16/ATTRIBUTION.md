# Attribution and license status

The maximum-search strategy and unary-hole starting point are due to
Charlie Reams's 23-state weak-Collatz construction in
[calr3/tinycryptids](https://github.com/calr3/tinycryptids/tree/c73bbd5377d4a06285660c170fccea56cf724155/weakcollatz),
pinned to commit `c73bbd5377d4a06285660c170fccea56cf724155`.

The released 16-state table redesigns the arithmetic and tape endpoints.
Its proof establishes the new table directly; the upstream theorem for the
23-state machine does not certify this redesign.

[`Arithmetic.lean`](../shared/proofs/Arithmetic.lean) adapts the bounded-round induction and
least-cycle-maximum proof structure from upstream
[`lean/TinyCryptids/WeakCollatz/Spec.lean`](https://github.com/calr3/tinycryptids/blob/c73bbd5377d4a06285660c170fccea56cf724155/lean/TinyCryptids/WeakCollatz/Spec.lean),
using the shortcut map and checking it with Lean 4.30.0. Attribution is also
retained in that source file. The unused upstream source files are not
vendored; the release builds without importing them.

## License choice

No repository-wide license has been selected. Public availability is not
an additional license grant. A root license choice remains with the
repository owner; no third-party source is relicensed by this notice.
