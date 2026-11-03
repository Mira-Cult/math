# 16-state binary Collatz cycle detector

These machines use one two-way infinite tape indexed by the integers, symbols
`0` and `1`, and blank `0`. Every transition writes a bit, moves one cell
left or right, and enters its next state. `Z` alone halts. The state counts
exclude Z. No minimality or record claim is made.

Each `.tm` file uses underscore-separated rows, in alphabetical state order;
a row gives its read-0 transition followed by its read-1 transition.
For example, `1RH` writes 1, moves right, and enters working state H.

Exact table: [collatz-cycle16.tm](collatz-cycle16.tm).
Working states are A–P. Start in A at coordinate 0 on the entirely blank tape.

The canonical C(M,v), for M≥2 and 1≤v≤M, has state D, head 0, and ones
precisely on [0,M−1] except for a hole at v−1. Every other cell is zero.
Initialization reaches C(2,2) in exactly four transitions. Checked macros:

- v=1: reaches C(M+1,M+1).
- v=2k: reaches C(M,k).
- v=2k+1, k≥1: put y=3k+2. For y<M, reaches C(M,y); for y=M,
  halts; for y>M, reaches C(M+1,M+1).

All returning macros have positive finite duration, full tape and head
equality, and no premature halt. The equality branch additionally proves
the entire halted configuration: head M+1, tape equal to C(M,M)'s tape.

The final theorems in [SixteenMain.lean](proofs/SixteenMain.lean) are:

```lean
-- In namespace CollatzTM.M16:
halts_iff_shortcut_cycle :
  Halts delta blank ↔ Arithmetic.ShortcutCounter

halts_iff_ordinary_cycle :
  Halts delta blank ↔ Arithmetic.OrdinaryCounter
```

With shortcut T(n)=n/2 for even n and (3n+1)/2 for odd n, the predicates are:

```lean
ShortcutCounter := ∃ n k, 3 ≤ n ∧ 0 < k ∧ iterate shortcut k n = n
OrdinaryCounter := ∃ n k, 0 < n ∧ 0 < k ∧ iterate ordinary k n = n ∧
  n ≠ 1 ∧ n ≠ 2 ∧ n ≠ 4
```

The proof uses a least nontrivial cycle maximum to show that earlier
candidate rounds finish. It explicitly excludes the shortcut cycle {1,2}
and the ordinary cycle {1,4,2}; shortcut 4 is proved nonperiodic.
An unbounded nonperiodic trajectory is outside this cycle-detection claim.


## Verification and source identity

This directory contains the writeup, [exact machine](collatz-cycle16.tm), machine-specific
[Lean sources](proofs/README.md), [provenance](PROVENANCE.json), and
[attribution](ATTRIBUTION.md). The shared arithmetic and tape library is an
explicit dependency in [the Collatz family](../shared/README.md), not a second
copy of the machine's proof.

From the repository root:

```sh
python3 turing-machines/collatz/scripts/check_release.py
python3 turing-machines/collatz/scripts/prepare_proofs.py --build --audit --kernel
python3 turing-machines/collatz/scripts/verify_finite.py
```

The assembler copies the pinned source bytes into an ignored build directory
with their original Lean module names. It does not generate or alter proofs.
See the [family verification guide](../README.md#verify-locally) for the pinned
toolchain, complete dependency and axiom audit, and finite-check scope.

[Back to the Collatz family](../README.md).
