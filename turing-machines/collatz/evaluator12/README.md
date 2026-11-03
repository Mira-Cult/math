# 12-state binary Collatz evaluator

These machines use one two-way infinite tape indexed by the integers, symbols
`0` and `1`, and blank `0`. Every transition writes a bit, moves one cell
left or right, and enters its next state. `Z` alone halts. The state counts
exclude Z. No minimality or record claim is made.

Each `.tm` file uses underscore-separated rows, in alphabetical state order;
a row gives its read-0 transition followed by its read-1 transition.
For example, `1RH` writes 1, moves right, and enters working state H.

Exact table: [collatz12.tm](collatz12.tm). Working states are A–L.
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

The final theorems in [TwelveMain.lean](proofs/TwelveMain.lean) are:

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


## Verification and source identity

This directory contains the writeup, [exact machine](collatz12.tm), machine-specific
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
