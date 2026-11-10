import PASoundness.M236GenericSweep

/-!
Symbolic pair blocks for a checked two-row sweep. This avoids reducing one
checker operation per pair when a long tape prefix is already represented by
a repeated pattern. The theorem retains the exact full zipper and word.
-/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.BulkSweep

open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.GenericSweep

def pairs (a b : Bool) : Nat → List Bool
  | 0 => []
  | n + 1 => a :: b :: pairs a b n

theorem pairs_shift (a b : Bool) (n : Nat) (tail : List Bool) :
    pairs a b n ++ (a :: b :: tail) = a :: b :: (pairs a b n ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [pairs, List.cons_append, ih]

/-- An arbitrary finite repeated pair prefix is traversed in two transitions
per pair, replacing it with the table's two writes and preserving all other
cells, including the entire zero background. -/
theorem right_block {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (first second : Bool)
    (hv : Valid m labels q first second .right)
    (count : Nat) (head : Int) (left tail : List Bool) :
    let a := m.table.row q first
    let b := m.table.row a.next second
    (system m labels).Block ⟨q, head, ⟨left, pairs first second count ++ tail⟩⟩ (2 * count)
      ⟨q, head + 2 * (count : Int), ⟨pairs b.write a.write count ++ left, tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero =>
    simpa [pairs] using WordEventSystem.Block.refl (system m labels) ⟨q, head, ⟨left, tail⟩⟩
  | succ count ih =>
    dsimp only
    let a := m.table.row q first
    let b := m.table.row a.next second
    let tape : Tape := ⟨left, pairs first second (count + 1) ++ tail⟩
    have hp0 : FiniteTape.read tape = first := by simp [tape, pairs, FiniteTape.read]
    have hp1 : FiniteTape.read (move .right tape a.write) = second := by
      simp [tape, pairs, FiniteTape.read, move, moveRight]
    have hpair := pair_sound m labels q first second .right head tape hv hp0 hp1
    have htail := ih (head + 2) (b.write :: a.write :: left)
    have hmove : pairNext m q first second .right tape =
        ⟨b.write :: a.write :: left, pairs first second count ++ tail⟩ := by
      simp [pairNext, a, b, move, moveRight, tape, pairs]
    rw [hmove] at hpair
    have hwhole := hpair.trans (system m labels) htail
    have ht : 2 + 2 * count = 2 * (count + 1) := by omega
    have hh : head + 2 + 2 * (count : Int) = head + 2 * ((count + 1 : Nat) : Int) := by omega
    dsimp only [a, b, tape] at hwhole
    simpa only [List.nil_append, List.cons_append, ht, hh, pairs, pairs_shift] using hwhole

/-- The leftward form retains the unread head bit and records both writes in
the right zipper. The finite left prefix is assumed explicitly. -/
theorem left_block {n : Nat} (m : Machine n) (labels : BitLabels n)
    (q : Fin n) (first second : Bool)
    (hv : Valid m labels q first second .left)
    (count : Nat) (head : Int) (leftTail rightTail : List Bool) :
    let a := m.table.row q first
    let b := m.table.row a.next second
    (system m labels).Block
      ⟨q, head, ⟨pairs second first count ++ leftTail, first :: rightTail⟩⟩ (2 * count)
      ⟨q, head - 2 * (count : Int),
        ⟨leftTail, first :: (pairs b.write a.write count ++ rightTail)⟩⟩ [] := by
  induction count generalizing head rightTail with
  | zero =>
    simpa [pairs] using WordEventSystem.Block.refl (system m labels) ⟨q, head, ⟨leftTail, first :: rightTail⟩⟩
  | succ count ih =>
    dsimp only
    let a := m.table.row q first
    let b := m.table.row a.next second
    let tape : Tape := ⟨pairs second first (count + 1) ++ leftTail, first :: rightTail⟩
    have hp0 : FiniteTape.read tape = first := by simp [tape, FiniteTape.read]
    have hp1 : FiniteTape.read (move .left tape a.write) = second := by
      simp [tape, pairs, FiniteTape.read, move, moveLeft]
    have hpair := pair_sound m labels q first second .left head tape hv hp0 hp1
    have htail := ih (head - 2) (b.write :: a.write :: rightTail)
    have hmove : pairNext m q first second .left tape =
        ⟨pairs second first count ++ leftTail, first :: b.write :: a.write :: rightTail⟩ := by
      simp [pairNext, a, b, move, moveLeft, tape, pairs]
    rw [hmove] at hpair
    have hwhole := hpair.trans (system m labels) htail
    have ht : 2 + 2 * count = 2 * (count + 1) := by omega
    have hh : head - 2 - 2 * (count : Int) = head - 2 * ((count + 1 : Nat) : Int) := by omega
    dsimp only [a, b, tape] at hwhole
    simpa only [List.nil_append, List.cons_append, ht, hh, pairs, pairs_shift] using hwhole

/-- A checked symbolic block transfers to the physical two-way tape. -/
theorem physical_block {n : Nat} (m : Machine n) (labels : BitLabels n)
    (start finish : Configuration n) (c : Config n) (ticks : Nat)
    (hrel : Related start c) (hblock : (system m labels).Block start ticks finish []) :
    ∃ out, (machineWordSystem m labels).Block c ticks out [] ∧ Related finish out := by
  have hs := advance_sound m labels hrel ticks
  rw [hblock.endpoint, hblock.output] at hs
  exact ⟨(machineWordSystem m labels).advance c ticks, ⟨rfl, hs.2.symm⟩, hs.1⟩

/-- The actual raw table's state 1 traverses a repeated `10` prefix to
the right, without emitting an event. -/
theorem raw_right (count : Nat) (head : Int) (left tail : List Bool) :
    (system raw rawLabels).Block
      ⟨1, head, ⟨left, pairs true false count ++ tail⟩⟩ (2 * count)
      ⟨1, head + 2 * (count : Int), ⟨pairs false true count ++ left, tail⟩⟩ [] := by
  have h := right_block raw rawLabels 1 true false (by decide) count head left tail
  have ha : (raw.table.row 1 true).write = true := by decide
  have hb : (raw.table.row (raw.table.row 1 true).next false).write = false := by decide
  simpa only [ha, hb] using h

/-- The actual raw table's state 35 traverses the corresponding repeated
prefix to the left, without emitting an event. -/
theorem raw_left (count : Nat) (head : Int) (leftTail rightTail : List Bool) :
    (system raw rawLabels).Block
      ⟨35, head, ⟨pairs true false count ++ leftTail, false :: rightTail⟩⟩ (2 * count)
      ⟨35, head - 2 * (count : Int),
        ⟨leftTail, false :: (pairs true false count ++ rightTail)⟩⟩ [] := by
  have h := left_block raw rawLabels 35 false true (by decide) count head leftTail rightTail
  have ha : (raw.table.row 35 false).write = false := by decide
  have hb : (raw.table.row (raw.table.row 35 false).next true).write = true := by decide
  simpa only [ha, hb] using h

end PASoundness.M236.BulkSweep
