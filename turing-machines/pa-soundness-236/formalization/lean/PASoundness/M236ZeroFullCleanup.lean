import PASoundness.M236ZeroCleanup
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.DecrementReturn
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

private theorem false_shift (n : Nat) (tail : List Bool) :
    List.replicate n false ++ false :: tail = false :: (List.replicate n false ++ tail) := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [List.replicate_succ, List.cons_append, ih]

private theorem cleared (gap zeros : Nat) (left tail : List Bool) :
    moveLeft ⟨List.replicate gap false ++ false ::
      (List.replicate zeros false ++ true :: left), false :: tail⟩ false =
    ⟨List.replicate (gap + zeros) false ++ true :: left, false :: false :: tail⟩ := by
  rw [false_shift]
  simp only [moveLeft, List.drop_succ_cons, List.drop_zero, List.headD_cons]
  congr 1
  rw [← List.append_assoc, List.replicate_append_replicate]

theorem zero_filled_cleanup (gap scratch1 scratch2 : Nat) (values : List Nat)
    (head : Int) (left tail : List Bool) :
    rawSystem.Block
      ⟨68, head, moveLeft ⟨List.replicate scratch2 true ++ false :: left,
        false :: (List.replicate scratch1 false ++ false :: false :: (bank (gap :: values) ++ tail))⟩ false⟩
      ((scratch2 + 1) + ((scratch2 + scratch1 + 3) + gap + 2) +
        ((gap + (scratch2 + scratch1 + 3)) + 2))
      ⟨64, head - (scratch2 : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++
          true :: false :: (bank values ++ tail))⟩ true⟩ [] := by
  let zeros := scratch2 + scratch1 + 3
  have he := UnaryCleanup.erase_left_stop scratch2 head left
    (List.replicate scratch1 false ++ false :: false :: (bank (gap :: values) ++ tail))
  have hzeros : List.replicate scratch2 false ++ false ::
      (List.replicate scratch1 false ++ false :: false :: (bank (gap :: values) ++ tail)) =
      List.replicate zeros false ++ true :: (List.replicate gap true ++ false :: (bank values ++ tail)) := by
    simp [zeros, bank, List.replicate_succ, ← List.replicate_append_replicate, false_shift, List.append_assoc]
  rw [hzeros] at he
  have hs := UnaryCleanup.seek_and_erase zeros gap (head - (scratch2 : Int) + 1)
    (true :: left) (bank values ++ tail)
  have hb := he.trans rawSystem hs
  rw [cleared] at hb
  have hr := UnaryAnchor.restore_and_scan (gap + zeros)
    (head - (scratch2 : Int) + 1 + (zeros : Int) + (gap : Int)) left
    (false :: (bank values ++ tail))
  have hf := hb.trans rawSystem hr
  have hh : head - (scratch2 : Int) + 1 + (zeros : Int) + (gap : Int) -
      ((gap + zeros : Nat) : Int) - 2 = head - (scratch2 : Int) - 1 := by omega
  simpa only [List.nil_append, hh, zeros] using hf

/-- Lift the filled-gap cleanup to the literal raw and quotient tables. -/
theorem physical_zero_filled_cleanup (gap scratch1 scratch2 : Nat) (values : List Nat)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨68, head, moveLeft ⟨List.replicate scratch2 true ++ false :: left,
      false :: (List.replicate scratch1 false ++ false :: false :: (bank (gap :: values) ++ tail))⟩ false⟩ c) :
    ∃ finish,
      (machineWordSystem raw rawLabels).Block c
        ((scratch2 + 1) + ((scratch2 + scratch1 + 3) + gap + 2) + ((gap + (scratch2 + scratch1 + 3)) + 2)) finish [] ∧
      Related ⟨64, head - (scratch2 : Int) - 1,
        moveLeft ⟨left, true :: (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++
          true :: false :: (bank values ++ tail))⟩ true⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((scratch2 + 1) + ((scratch2 + scratch1 + 3) + gap + 2) + ((gap + (scratch2 + scratch1 + 3)) + 2))
        (mapConfig finish) [] ∧
      0 < (scratch2 + 1) + ((scratch2 + scratch1 + 3) + gap + 2) + ((gap + (scratch2 + scratch1 + 3)) + 2) := by
  have hb := zero_filled_cleanup gap scratch1 scratch2 values head left tail
  obtain ⟨finish, hp, hr⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨finish, hp, hr, BootstrapScan.mapped_block hp, by omega⟩

private theorem bank_zero_split (gap : Nat) (before after : List Nat) (tail : List Bool) :
    bank (gap :: before) ++ true :: false :: (bank after ++ tail) =
      bank (gap :: (before ++ 0 :: after)) ++ tail := by
  simp [bank, UnaryIncrement.bank_append, List.append_assoc]

/-- The selected zero register returns to the grammar root with the entire
unary bank unchanged. The two scratch runs and residual counter prefix are
explicit; this theorem does not establish source reachability. -/
theorem physical_zero_root (r : Fin 9) (gap scratch1 scratch2 : Nat)
    (before after : List Nat) (hlen : before.length = r.val)
    (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool)
    (hprefix : counterPush runs [] = true :: bit :: pcTail)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨List.replicate scratch1 true ++ false ::
        (List.replicate scratch2 true ++ false ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left)),
        true :: false :: (bank (gap :: before) ++ true :: false :: (bank after ++ tail))⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++
            true :: false :: (bank (before ++ 0 :: after) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  let pre := counterWord runs ++ List.replicate 6 false ++ false :: left
  let h68 := head + 2 + (shiftTime (gap :: before) : Int) - 1 -
    (shiftTime (gap :: before).reverse : Int) - 2 - (scratch1 : Int) - 1
  let suffix := List.replicate (gap + (scratch2 + scratch1 + 3)) false ++
    true :: false :: (bank (before ++ 0 :: after) ++ tail)
  obtain ⟨mid1, hp1, hr1, hq1, ht1⟩ :=
    physical_zero_cleanup_entry r gap scratch1 before hlen head
      (List.replicate scratch2 true ++ false :: pre) (bank after ++ tail) c hrel
  rw [bank_zero_split] at hr1
  obtain ⟨mid2, hp2, hr2, hq2, ht2⟩ :=
    physical_zero_filled_cleanup gap scratch1 scratch2 (before ++ 0 :: after) h68 pre tail mid1 hr1
  let h64 := h68 - (scratch2 : Int) - 1
  obtain ⟨mid3, hp3, hr3, hq3, ht3⟩ :=
    physical_counter runs h64 (false :: left) suffix mid2 hr2
  have hcontrol : counterPush runs suffix = true :: bit :: (pcTail ++ suffix) := by
    have h := counterPush_append runs [] suffix
    simpa [hprefix] using h
  rw [hcontrol] at hr3
  let h65 := h64 - (counterTime runs : Int) - 6
  have hroot : Related ⟨65, h65,
      ⟨left, List.replicate 7 false ++ true :: true :: bit :: (pcTail ++ suffix)⟩⟩ mid3 := by
    simpa [h65, moveLeft, List.replicate_succ] using hr3
  have hb := root_reentry 7 bit h65 left (pcTail ++ suffix)
  obtain ⟨finish, hp4, hr4⟩ := BulkSweep.physical_block raw rawLabels _ _ mid3 10 hroot hb
  let t1 := shiftTime (gap :: before) + 2 + 3 + (shiftTime (gap :: before).reverse + 2) + (scratch1 + 1)
  let t2 := (scratch2 + 1) + ((scratch2 + scratch1 + 3) + gap + 2) + ((gap + (scratch2 + scratch1 + 3)) + 2)
  refine ⟨t1 + t2 + (counterTime runs + 6) + 10, h65 + 10, finish, ?_, ?_, ?_, ?_⟩
  · dsimp [t1, t2]; omega
  · simpa [t1, t2] using ((hp1.trans (machineWordSystem raw rawLabels) hp2).trans
      (machineWordSystem raw rawLabels) hp3).trans (machineWordSystem raw rawLabels) hp4
  · simpa [h65, h64, h68, suffix, Int.add_assoc] using hr4
  · simpa [t1, t2] using ((hq1.trans (machineWordSystem machine machineLabels) hq2).trans
      (machineWordSystem machine machineLabels) hq3).trans (machineWordSystem machine machineLabels)
        (BootstrapScan.mapped_block hp4)

/-- A zero-valued selected register leaves the independently specified nine
register bank and reserve unchanged on return to the grammar root. -/
theorem physical_named_zero_root (registers : RegisterMachine.Bank 9) (r : Fin 9)
    (hzero : registers r = 0) (reserve : List Nat) (gap scratch1 scratch2 : Nat)
    (runs : List (Fin 6)) (bit : Bool) (pcTail : List Bool)
    (hprefix : counterPush runs [] = true :: bit :: pcTail)
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨DecrementSelector.entryState r, head,
      ⟨List.replicate scratch1 true ++ false ::
        (List.replicate scratch2 true ++ false ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left)),
        true :: false :: (bank (gap :: UnaryIncrementNine.before registers r) ++ true :: false ::
          (bank (UnaryIncrementNine.after registers r ++ reserve) ++ tail))⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          pcTail ++ (List.replicate (gap + (scratch2 + scratch1 + 3)) false ++
            true :: false :: (bank (UnaryNine.values registers ++ reserve) ++ tail))⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] ∧
      UnaryCodec.decodeBank (9 + reserve.length) (bank (UnaryNine.values registers ++ reserve) ++ tail) =
        some (UnaryNine.values registers ++ reserve, tail) ∧
      RegisterMachine.execute (.decNZ r) registers = ⟨registers, false, []⟩ := by
  obtain ⟨time, endHead, finish, ht, hp, hr, hq⟩ :=
    physical_zero_root r gap scratch1 scratch2 (UnaryIncrementNine.before registers r)
      (UnaryIncrementNine.after registers r ++ reserve) (Selector.before_length registers r)
      runs bit pcTail hprefix head left tail c hrel
  have hv : UnaryIncrementNine.before registers r ++ 0 :: (UnaryIncrementNine.after registers r ++ reserve) =
      UnaryNine.values registers ++ reserve := by
    rw [UnaryIncrementNine.values_split registers r, hzero]
    simp [List.append_assoc]
  rw [hv] at hr
  refine ⟨time, endHead, finish, ht, hp, hr, hq, ?_, RegisterMachine.decNZ_zero registers r hzero⟩
  simpa only [List.length_append, UnaryNine.values_length] using
    UnaryCodec.decode_bank (UnaryNine.values registers ++ reserve) tail

example : rawSystem.Block
    ⟨57, 0, ⟨[false, false, false, true, true, false, false, false, false, false, false, false],
      [true, false, true, false, true, false] ++ bank (List.replicate 8 0) ++ [false]⟩⟩ 42
    ⟨79, -2, ⟨[false, true, true, false, false, false, false, false, false, false],
      [true, false, false, false, true, false] ++ bank (List.replicate 9 0) ++ [false]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨57, 0, ⟨[false, false, false, true, true, false, false, false, false, false, false, false],
      [true, false, true, false, true, false] ++ bank (List.replicate 8 0) ++ [false]⟩⟩ 41
    ⟨79, -2, ⟨[false, true, true, false, false, false, false, false, false, false],
      [true, false, false, false, true, false] ++ bank (List.replicate 9 0) ++ [false]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨57, 0, ⟨[false, false, false, true, true, false, false, false, false, false, false, false],
        [true, false, true, false, true, false] ++ bank (List.replicate 8 0) ++ [false]⟩⟩ 41 ≠
      ⟨79, -2, ⟨[false, true, true, false, false, false, false, false, false, false],
        [true, false, false, false, true, false] ++ bank (List.replicate 9 0) ++ [false]⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.DecrementReturn
