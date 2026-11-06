import Mathlib.Tactic

/-! Arithmetic contract for the three-transfer swap in the NP=coNP 284-state
producer at Mira-Cult/math-wip commit
`7b90875183aa928fb19a4a9bf333b8ced2194ded`,
`problems/np-conp-formulations/selector/continuation/compact/phase_swap/PROOF.md`.

This is a finite abstract register calculation. It does not identify physical
rows, establish a zero work cell at either actual entry, or prove that the
literal table implements these operations. -/

namespace Shared.Beeping.NPcoNP.Swap284

/-- A retained DECNZ/INC transfer, with the final unsuccessful DECNZ counted.
The inputs are destination and source; the result is destination, source,
and the number of primitive applications. -/
def transfer (dst : Nat) : Nat → Nat × Nat × Nat
  | 0 => (dst, 0, 1)
  | src + 1 =>
      let (d, s, cost) := transfer (dst + 1) src
      (d, s, cost + 2)

theorem transfer_correct (dst src : Nat) :
    transfer dst src = (dst + src, 0, 2 * src + 1) := by
  induction src generalizing dst with
  | zero => simp [transfer]
  | succ n ih =>
    simp only [transfer, ih]
    congr 1 <;> omega

/-- Three distinct abstract carriers, listed as left, right, and work. -/
abbrev Store := Nat × Nat × Nat

def first (s : Store) : Store × Nat :=
  let (d, z, n) := transfer s.2.2 s.1
  ((z, s.2.1, d), n)

def second (s : Store) : Store × Nat :=
  let (d, z, n) := transfer s.1 s.2.1
  ((d, z, s.2.2), n)

def third (s : Store) : Store × Nat :=
  let (d, z, n) := transfer s.2.1 s.2.2
  ((s.1, d, z), n)

def swap (s : Store) : Store × Nat :=
  let (a, x) := first s
  let (b, y) := second a
  let (c, z) := third b
  (c, x + y + z)

theorem first_boundary (l r : Nat) :
    first (l, r, 0) = ((0, r, l), 2 * l + 1) := by
  simp [first, transfer_correct]

theorem second_boundary (l r : Nat) :
    second (0, r, l) = ((r, 0, l), 2 * r + 1) := by
  simp [second, transfer_correct]

theorem third_boundary (l r : Nat) :
    third (r, 0, l) = ((r, l, 0), 2 * l + 1) := by
  simp [third, transfer_correct]

/-- Correct value, restored work, and positive exact primitive count under
the external-entry work-zero premise. -/
theorem swap_correct (l r : Nat) :
    swap (l, r, 0) = ((r, l, 0), 4 * l + 2 * r + 3) := by
  simp only [swap, first_boundary, second_boundary, third_boundary]
  congr 1 <;> omega

theorem swap_positive (l r : Nat) : 0 < (swap (l, r, 0)).2 := by
  rw [swap_correct]
  simp

end Shared.Beeping.NPcoNP.Swap284
