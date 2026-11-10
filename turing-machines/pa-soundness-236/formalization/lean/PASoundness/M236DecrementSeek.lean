import PASoundness.M236DecrementSelector
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.DecrementSeek
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem true_shift (n : Nat) (tail : List Bool) :
    List.replicate n true ++ true :: tail = true :: (List.replicate n true ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

/-- State 29 passes an arbitrary run of ones without changing any cell. -/
theorem scan_ones (count : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨29, head, ⟨left, List.replicate count true ++ false :: tail⟩⟩ count
      ⟨29, head + (count : Int), ⟨List.replicate count true ++ left, false :: tail⟩⟩ [] := by
  induction count generalizing head left with
  | zero => simpa using WordEventSystem.Block.refl rawSystem ⟨29, head, ⟨left, false :: tail⟩⟩
  | succ count ih =>
    have hr : raw.table.row 29 true = ⟨true, .right, 29, false⟩ := by decide
    have he : rawLabels.at 29 true = none := by decide
    have hs : rawSystem.step
        ⟨29, head, ⟨left, List.replicate (count + 1) true ++ false :: tail⟩⟩ =
        (⟨29, head + 1, ⟨true :: left, List.replicate count true ++ false :: tail⟩⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hr, he,
        Move.apply, moveRight, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem (ih (head + 1) (true :: left))
    have hh : head + 1 + (count : Int) = head + ((count + 1 : Nat) : Int) := by omega
    simpa only [List.nil_append, hh, Nat.add_comm 1 count, List.replicate_succ,
      List.cons_append, true_shift] using hb

/-- A separator followed by another one is crossed in two silent steps. -/
theorem cross_separator (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨29, head, ⟨left, false :: true :: tail⟩⟩ 2
      ⟨29, head + 2, ⟨true :: false :: left, tail⟩⟩ [] := by
  have r29 : raw.table.row 29 false = ⟨false, .right, 30, false⟩ := by decide
  have e29 : rawLabels.at 29 false = none := by decide
  have r30 : raw.table.row 30 true = ⟨true, .right, 29, false⟩ := by decide
  have e30 : rawLabels.at 30 true = none := by decide
  have h0 : rawSystem.step ⟨29, head, ⟨left, false :: true :: tail⟩⟩ =
      (⟨30, head + 1, ⟨false :: left, true :: tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r29, e29, Move.apply, moveRight]
  have h1 : rawSystem.step ⟨30, head + 1, ⟨false :: left, true :: tail⟩⟩ =
      (⟨29, head + 2, ⟨true :: false :: left, tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r30, e30, Move.apply, moveRight]
    omega
  simpa [Int.add_assoc] using (WordEventSystem.Block.single rawSystem h0).trans rawSystem
    (WordEventSystem.Block.single rawSystem h1)

/-- The first double separator stops the scan at state 31. -/
theorem stop_double (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨29, head, ⟨left, false :: false :: tail⟩⟩ 2
      ⟨31, head, ⟨left, false :: false :: tail⟩⟩ [] := by
  have r29 : raw.table.row 29 false = ⟨false, .right, 30, false⟩ := by decide
  have e29 : rawLabels.at 29 false = none := by decide
  have r30 : raw.table.row 30 false = ⟨false, .left, 31, false⟩ := by decide
  have e30 : rawLabels.at 30 false = none := by decide
  have h0 : rawSystem.step ⟨29, head, ⟨left, false :: false :: tail⟩⟩ =
      (⟨30, head + 1, ⟨false :: left, false :: tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r29, e29, Move.apply, moveRight]
  have h1 : rawSystem.step ⟨30, head + 1, ⟨false :: left, false :: tail⟩⟩ =
      (⟨31, head, ⟨left, false :: false :: tail⟩⟩, []) := by
    simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, r30, e30, Move.apply, moveLeft]
  simpa using (WordEventSystem.Block.single rawSystem h0).trans rawSystem (WordEventSystem.Block.single rawSystem h1)

/-- Full left zipper after scanning the encoded suffix in order. -/
def seekLeft : List Nat → List Bool → List Bool
  | [], left => left
  | value :: rest, left => seekLeft rest (List.replicate value true ++ true :: false :: left)

/-- Scan an arbitrary finite unary suffix and stop on its first double zero. -/
theorem scan_suffix (values : List Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨29, head, ⟨left, false :: (bank values ++ false :: tail)⟩⟩
      (shiftTime values + 2)
      ⟨31, head + (shiftTime values : Int), ⟨seekLeft values left, false :: false :: tail⟩⟩ [] := by
  induction values generalizing head left with
  | nil => simpa [bank, shiftTime, seekLeft] using stop_double head left tail
  | cons value rest ih =>
    have hc := cross_separator head left (List.replicate value true ++ false :: (bank rest ++ false :: tail))
    have ho := scan_ones value (head + 2) (true :: false :: left) (bank rest ++ false :: tail)
    have hr := ih (head + 2 + (value : Int))
      (List.replicate value true ++ true :: false :: left)
    have hb := (hc.trans rawSystem ho).trans rawSystem hr
    have hh : head + 2 + (value : Int) + (shiftTime rest : Int) =
        head + ((value + 2 + shiftTime rest : Nat) : Int) := by omega
    have ht : 2 + value + (shiftTime rest + 2) = value + 2 + shiftTime rest + 2 := by omega
    simpa only [bank, shiftTime, seekLeft, List.cons_append, List.nil_append, List.append_assoc, hh, ht] using hb

/-- A positive selected value reaches the backward-shift state after a
finite scan of every subsequent register block. -/
theorem positive_seek (value : Nat) (after : List Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨8, head,
      ⟨left, true :: true :: (List.replicate value true ++ false :: (bank after ++ false :: tail))⟩⟩
      (2 + value + (shiftTime after + 2))
      ⟨31, head + 2 + (value : Int) + (shiftTime after : Int),
        ⟨seekLeft after (List.replicate value true ++ true :: false :: left), false :: false :: tail⟩⟩ [] := by
  have hp := DecrementSelector.positive_branch head left
    (List.replicate value true ++ false :: (bank after ++ false :: tail))
  have ho := scan_ones value (head + 2) (true :: false :: left) (bank after ++ false :: tail)
  have hs := scan_suffix after (head + 2 + (value : Int))
    (List.replicate value true ++ true :: false :: left) tail
  simpa only [List.nil_append] using (hp.trans rawSystem ho).trans rawSystem hs

/-- Selection and positive-value scanning refine the raw and quotient tables;
the later backward shift and control return are separate. -/
theorem physical_positive_seek (r : Fin 9) (gap : Nat) (before : List Nat)
    (hlen : before.length = r.val) (value : Nat) (after : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨left, true :: false :: (bank (gap :: before) ++ true :: true ::
        (List.replicate value true ++ false :: (bank after ++ false :: tail)))⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c
        (shiftTime (gap :: before) + 2 + (2 + value + (shiftTime after + 2))) finish [] ∧
      Related ⟨31, head + 2 + (shiftTime (gap :: before) : Int) + 2 +
          (value : Int) + (shiftTime after : Int),
        ⟨seekLeft after (List.replicate value true ++ true :: false ::
          ((bank (gap :: before)).reverse ++ false :: false :: left)), false :: false :: tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (shiftTime (gap :: before) + 2 + (2 + value + (shiftTime after + 2))) (mapConfig finish) [] ∧
      0 < shiftTime (gap :: before) + 2 + (2 + value + (shiftTime after + 2)) := by
  have hs := DecrementSelector.entry_block r gap before hlen head left
    (true :: true :: (List.replicate value true ++ false :: (bank after ++ false :: tail)))
  have hp := positive_seek value after (head + 2 + (shiftTime (gap :: before) : Int))
    ((bank (gap :: before)).reverse ++ false :: false :: left) tail
  have hb := hs.trans rawSystem hp
  simp only [List.nil_append] at hb
  obtain ⟨finish, hp', hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨finish, hp', hr, BootstrapScan.mapped_block hp', by omega⟩

example : rawSystem.Block ⟨57, 0, ⟨[], [true, false, true, false, true, true, false, false]⟩⟩ 8
    ⟨31, 6, ⟨[true, false, false, true, false, false], [false, false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block ⟨57, 0, ⟨[], [true, false, true, false, true, true, false, false]⟩⟩ 7
    ⟨31, 6, ⟨[true, false, false, true, false, false], [false, false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance ⟨57, 0, ⟨[], [true, false, true, false, true, true, false, false]⟩⟩ 7 ≠
    ⟨31, 6, ⟨[true, false, false, true, false, false], [false, false]⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.DecrementSeek
