import PASoundness.M236Selector

/-! Return from a prepared filled-gap register operation. The first unary run
contains the filled gap and the anchor; cleanup erases that run and restores
its final anchor cell. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.SelectorReturn
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift

private theorem cleared_tape (gap scratch : Nat) (left tail : List Bool) :
    moveLeft ⟨List.replicate gap false ++ false ::
      (List.replicate (scratch + 2) false ++ true :: left), false :: tail⟩ false =
    ⟨List.replicate (gap + scratch + 2) false ++ true :: left, false :: false :: tail⟩ := by
  have heq : List.replicate gap false ++ false ::
      (List.replicate (scratch + 2) false ++ true :: left) =
      false :: (List.replicate (gap + scratch + 2) false ++ true :: left) := by
    have hn : gap + (scratch + 3) = (gap + scratch + 2) + 1 := by omega
    calc
      _ = (List.replicate gap false ++ List.replicate (scratch + 3) false) ++ true :: left := by
        simp [List.replicate_succ, List.append_assoc]
      _ = List.replicate (gap + (scratch + 3)) false ++ true :: left := by
        rw [List.replicate_append_replicate]
      _ = false :: (List.replicate (gap + scratch + 2) false ++ true :: left) := by
        rw [hn, List.replicate_succ]
        rfl
  simp [moveLeft, heq]

/-- Cleanup of an arbitrary filled gap restores the final one-cell anchor and
keeps the complete following bank unchanged before entering state 64. -/
theorem filled_cleanup (gap scratch : Nat) (values : List Nat) (head : Int)
    (left tail : List Bool) :
    rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (gap :: values) ++ tail)⟩ false⟩
      (3 * scratch + 2 * gap + 9)
      ⟨64, head - (scratch : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate (gap + scratch + 2) false ++
          true :: false :: (bank values ++ tail))⟩ true⟩ [] := by
  have hraw := UnaryCleanup.cleanup_block scratch gap values head left tail
  rw [cleared_tape] at hraw
  have hrest := UnaryAnchor.restore_and_scan (gap + scratch + 2) (head + (gap : Int) + 3) left
    (false :: (bank values ++ tail))
  have hb := hraw.trans rawSystem hrest
  have ht : (2 * scratch + gap + 5) + ((gap + scratch + 2) + 2) =
      3 * scratch + 2 * gap + 9 := by omega
  have hh : head + (gap : Int) + 3 - ((gap + scratch + 2 : Nat) : Int) - 2 =
      head - (scratch : Int) - 1 := by omega
  simpa only [List.nil_append, ht, hh] using hb

/-- The filled-gap return also holds on the complete raw and quotient tapes. -/
theorem physical_filled_cleanup (gap scratch : Nat) (values : List Nat) (head : Int)
    (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨68, head, moveLeft ⟨List.replicate scratch true ++ false :: left,
        false :: false :: (bank (gap :: values) ++ tail)⟩ false⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c (3 * scratch + 2 * gap + 9) finish [] ∧
      Related ⟨64, head - (scratch : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate (gap + scratch + 2) false ++
          true :: false :: (bank values ++ tail))⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (3 * scratch + 2 * gap + 9) (mapConfig finish) [] ∧ 0 < 3 * scratch + 2 * gap + 9 := by
  have hb := filled_cleanup gap scratch values head left tail
  obtain ⟨finish, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨finish, hp, hr, BootstrapScan.mapped_block hp, by omega⟩

/-- From a named prepared increment entry, select the indexed register,
increment it and restore the filled-gap anchor. The exact full-tape
precondition is explicit; no source reachability is assumed. -/
theorem physical_named_increment
    (registers : RegisterMachine.Bank 9) (r : Fin 9) (reserve : List Nat)
    (gap scratch : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related
      ⟨Selector.entryState r, head,
        ⟨List.replicate scratch true ++ false :: left,
          true :: false :: (bank (gap :: UnaryIncrementNine.before registers r) ++
            (List.replicate (registers r + 1) true ++ false ::
              (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)))⟩⟩ c) :
    ∃ (first : Nat) (values : List Nat) (selected middle finish : Config 237),
      (UnaryIncrementNine.after registers r ++ reserve).reverse ++
        (registers r + 1) :: (gap :: UnaryIncrementNine.before registers r).reverse = first :: values ∧
      (machineWordSystem raw rawLabels).Block c
        (shiftTime (gap :: UnaryIncrementNine.before registers r) + 2) selected [] ∧
      (machineWordSystem raw rawLabels).Block c
        (shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
          (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
            (first + 1 + (shiftTime values + 2)))) middle [] ∧
      (machineWordSystem raw rawLabels).Block c
        (shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
          (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
            (first + 1 + (shiftTime values + 2))) + (3 * scratch + 2 * gap + 9)) finish [] ∧
      Related
        ⟨64, head + 2 + (shiftTime (gap :: UnaryIncrementNine.before registers r) : Int) +
          ((registers r + 2 : Nat) : Int) + (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
          ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2 - (scratch : Int) - 1,
          moveLeft ⟨left, true :: (List.replicate (gap + scratch + 2) false ++ true :: false ::
            (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail))⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
          (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
            (first + 1 + (shiftTime values + 2))) + (3 * scratch + 2 * gap + 9))
        (mapConfig finish) [] ∧
      0 < shiftTime (gap :: UnaryIncrementNine.before registers r) + 2 +
          (UnaryIncrement.duration (registers r) (UnaryIncrementNine.after registers r ++ reserve) +
            (first + 1 + (shiftTime values + 2))) + (3 * scratch + 2 * gap + 9) ∧
      UnaryCodec.decodeBank (9 + reserve.length)
        (bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) ++ tail) =
        some (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve, tail) := by
  let suffix := List.replicate (registers r + 1) true ++ false ::
    (bank (UnaryIncrementNine.after registers r ++ reserve) ++ false :: tail)
  obtain ⟨selected, hs, hrs, hqs, _⟩ := Selector.physical_entry r gap
    (UnaryIncrementNine.before registers r) (Selector.before_length registers r) head
    (List.replicate scratch true ++ false :: left) suffix c hrel
  obtain ⟨first, values, middle, he, hi, hri, hqi, _, _⟩ :=
    UnaryReturn.physical_increment_return (gap :: UnaryIncrementNine.before registers r) (registers r)
      (UnaryIncrementNine.after registers r ++ reserve)
      (head + 2 + (shiftTime (gap :: UnaryIncrementNine.before registers r) : Int))
      (List.replicate scratch true ++ false :: left) tail selected hrs
  have hvalues : (gap :: UnaryIncrementNine.before registers r) ++ (registers r + 1) ::
        (UnaryIncrementNine.after registers r ++ reserve) =
      gap :: (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) := by
    rw [UnaryIncrementNine.values_increment]
    simp [List.append_assoc]
  rw [hvalues] at hri
  obtain ⟨finish, hc, hrc, hqc, _⟩ := physical_filled_cleanup gap scratch
    (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve)
    (head + 2 + (shiftTime (gap :: UnaryIncrementNine.before registers r) : Int) +
      ((registers r + 2 : Nat) : Int) + (shiftTime (UnaryIncrementNine.after registers r ++ reserve) : Int) - 1 -
      ((first + 1 : Nat) : Int) - (shiftTime values : Int) - 2) left tail middle hri
  have hsi := hs.trans (machineWordSystem raw rawLabels) hi
  have hqi' := hqs.trans (machineWordSystem machine machineLabels) hqi
  refine ⟨first, values, selected, middle, finish, he, hs, ?_, ?_, hrc, ?_, by omega, ?_⟩
  · simpa using hsi
  · simpa using hsi.trans (machineWordSystem raw rawLabels) hc
  · simpa using hqi'.trans (machineWordSystem machine machineLabels) hqc
  · simpa only [List.length_append, UnaryNine.values_length] using
      UnaryCodec.decode_bank (UnaryNine.values (RegisterMachine.execute (.inc r) registers).bank ++ reserve) tail

end PASoundness.M236.SelectorReturn
