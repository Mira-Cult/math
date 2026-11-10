import PASoundness.M236DecrementReturn
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.DecrementReturn
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem false_shift (n : Nat) (tail : List Bool) :
    List.replicate n false ++ false :: tail = false :: (List.replicate n false ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

theorem erase_scratch (scratch : Nat) (head : Int) (left right : List Bool) :
    rawSystem.Block
      ⟨69, head, moveLeft ⟨List.replicate scratch true ++ false :: left, false :: right⟩ false⟩
      (scratch + 1)
      ⟨68, head - (scratch : Int) - 1,
        moveLeft ⟨left, false :: (List.replicate scratch false ++ false :: right)⟩ false⟩ [] := by
  induction scratch generalizing head right with
  | zero =>
    have hr : raw.table.row 69 false = ⟨false, .left, 68, false⟩ := by decide
    have he : rawLabels.at 69 false = none := by decide
    have hs : rawSystem.step ⟨69, head, ⟨left, false :: false :: right⟩⟩ =
        (⟨68, head - 1, moveLeft ⟨left, false :: false :: right⟩ false⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hr, he, Move.apply]
    simpa [moveLeft] using WordEventSystem.Block.single rawSystem hs
  | succ scratch ih =>
    have hr : raw.table.row 69 true = ⟨false, .left, 69, false⟩ := by decide
    have he : rawLabels.at 69 true = none := by decide
    have hs : rawSystem.step
        ⟨69, head, moveLeft ⟨List.replicate (scratch + 1) true ++ false :: left, false :: right⟩ false⟩ =
        (⟨69, head - 1, moveLeft ⟨List.replicate scratch true ++ false :: left,
          false :: false :: right⟩ false⟩, []) := by
      simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hr, he,
        Move.apply, moveLeft, List.replicate_succ]
    have hb := (WordEventSystem.Block.single rawSystem hs).trans rawSystem (ih (head - 1) (false :: right))
    have hh : head - 1 - (scratch : Int) - 1 = head - ((scratch + 1 : Nat) : Int) - 1 := by omega
    simpa [List.replicate_succ, hh, Nat.add_comm, Nat.add_assoc, false_shift] using hb

/-- After the zero test, return across the bank and erase the finite scratch
run, reaching raw state 68 with the full tape recorded. -/
theorem physical_zero_cleanup_entry (r : Fin 9) (gap scratch : Nat) (before : List Nat)
    (hlen : before.length = r.val) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨List.replicate scratch true ++ false :: left,
        true :: false :: (bank (gap :: before) ++ true :: false :: tail)⟩⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c
        (shiftTime (gap :: before) + 2 + 3 + (shiftTime (gap :: before).reverse + 2) + (scratch + 1)) finish [] ∧
      Related ⟨68, head + 2 + (shiftTime (gap :: before) : Int) - 1 -
          (shiftTime (gap :: before).reverse : Int) - 2 - (scratch : Int) - 1,
        moveLeft ⟨left, false :: (List.replicate scratch false ++ false :: false ::
          (bank (gap :: before) ++ true :: false :: tail))⟩ false⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (shiftTime (gap :: before) + 2 + 3 + (shiftTime (gap :: before).reverse + 2) + (scratch + 1))
        (mapConfig finish) [] ∧
      0 < shiftTime (gap :: before) + 2 + 3 + (shiftTime (gap :: before).reverse + 2) + (scratch + 1) := by
  obtain ⟨middle, hp, hr, hq, ht⟩ :=
    physical_zero_return r gap before hlen head (List.replicate scratch true ++ false :: left) tail c hrel
  have hb := erase_scratch scratch
    (head + 2 + (shiftTime (gap :: before) : Int) - 1 - (shiftTime (gap :: before).reverse : Int) - 2)
    left (false :: (bank (gap :: before) ++ true :: false :: tail))
  obtain ⟨finish, hpr, hrr⟩ := BulkSweep.physical_block raw rawLabels _ _ middle _ hr hb
  refine ⟨finish, ?_, hrr, ?_, by omega⟩
  · simpa using hp.trans (machineWordSystem raw rawLabels) hpr
  · simpa using hq.trans (machineWordSystem machine machineLabels) (BootstrapScan.mapped_block hpr)
end PASoundness.M236.DecrementReturn
