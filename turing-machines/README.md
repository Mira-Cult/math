# Two exact binary Collatz Turing machines

Both machines use one two-way infinite tape indexed by the integers, symbols
`0` and `1`, and blank `0`. Every transition writes a bit, moves one cell
left or right, and enters its next state. `Z` alone halts. The state counts
exclude Z. No minimality or record claim is made.

Each `.tm` file uses underscore-separated rows, in alphabetical state order;
a row gives its read-0 transition followed by its read-1 transition.
For example, `1RH` writes 1, moves right, and enters working state H.

## 12-state input evaluator

Exact table: [collatz12.tm](machines/collatz12.tm). Working states are A–L.
For a positive integer n, write its binary bits least significant first and
encode each bit b as the two tape cells `1b`. All other cells are 0.
Start in A on the first marker, at any integer offset p. For example,
13 has reading-order bits `1,0,1,1`, so its input is `11 10 11 11`.

Let E(n,p) be that complete configuration. The checked macros are:

| Input | Complete result | Transitions |
| --- | --- | ---: |
| n = 1 | Halt, blank tape, head p+1 | 3 |
| Even n > 1 | E(n/2,p+2) | 2 |
| Odd n > 1 | E((3n+1)/2,p+2) | 4·bitlength((3n+1)/2)+4 |

The stated timing is proved, with positive bitlength equal to
`Nat.log2 n + 1`. All macros include full tape equality and no earlier halt.

The final theorems in [TwelveMain.lean](proofs/CollatzTM/TwelveMain.lean) are:

```lean
-- In namespace CollatzTM.M12, with Arithmetic open:
halts_iff_collatz (n : Nat) (p : Int) (hn : 0 < n) :
  Halts delta (canonicalNat n p) ↔ ∃ k, uit k n = 1

totality_iff_collatz :
  (∀ n, 0 < n → Halts delta (canonicalNat n 0)) ↔
  (∀ n, 0 < n → ∃ k, uit k n = 1)
```

Here `uit` iterates the ordinary Collatz map U(n)=n/2 for even n and 3n+1
for odd n. Thus this machine's universal positive-input termination is
equivalent to the ordinary Collatz conjecture. The conjecture is not asserted.

## 16-state blank-tape cycle detector

Exact table: [collatz-cycle16.tm](machines/collatz-cycle16.tm).
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

The final theorems in [SixteenMain.lean](proofs/CollatzTM/SixteenMain.lean) are:

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

## Verify locally

Install the pinned Lean toolchain `leanprover/lean4:v4.30.0` using
[elan](https://github.com/leanprover/elan), then run from the repository root:

```sh
python3 turing-machines/scripts/check_release.py
cd turing-machines/proofs
lake build
lake env lean Audit.lean
lake env leanchecker --fresh CollatzTM
```

The Lake package has no third-party dependencies. The imported standard
library comes with Lean 4.30.0. `leanchecker --fresh` replays the complete
imported environment through the same Lean kernel; it is not an external
proof assistant. No CI workflows are included.

`Audit.lean` prints exact theorem types and transitive axiom dependencies.
The final equivalences depend only on Lean's standard `propext`,
`Classical.choice`, and `Quot.sound`. There are no proof placeholders or new
axioms in their dependency closures. Both concrete machine specifications
are proved, so no macro-specification hypotheses remain in the final results.

The tape model is the complete function `Int → Bool`, with finite support
proved for canonical inputs and preserved through finite runs. `Reaches`
combines exact configuration equality with exclusion of every earlier halt.
`TableAudit.lean` reconstructs the exact strings from the actual transition
functions and proves that the unique halt transitions are L0 and O0.

Optional independent finite corroboration, from the repository root:

```sh
python3 turing-machines/scripts/verify_finite.py
```

This checks 65,535 evaluator inputs and 5,049 canonical cycle-detector inputs.
These finite checks do not replace the general proofs.

## Source identity and attribution

All 22 Lean source files are byte-identical to audited source snapshot
`b6c17e92bb9f0f4ba070190e17e17a24fe789ec6`. This snapshot identifier refers
to the proof-development history, not an ancestor in this release repository.
Public source hashes and exact machine hashes are in [PROVENANCE.json](PROVENANCE.json).
The check script validates these hashes, the import inventory, and each `.tm`
against the corresponding compiled table's source string. Kernel checking of
the actual table equality is performed by `TableAudit.lean`.

The release includes the authored proofs, exact tables, and local verification
scripts. See [ATTRIBUTION.md](ATTRIBUTION.md) for Michel's 12-state origin,
Reams's search strategy, the pinned upstream proof influence, and license status.
