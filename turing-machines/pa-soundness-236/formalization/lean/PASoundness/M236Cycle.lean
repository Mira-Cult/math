import PASoundness.M236CycleCore
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Redispatch
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- From a specified root tape, follow the named path, fill a finite clean
gap, return to root and follow the same path a second time. -/
theorem root_prepare_redispatch (r : Fin 9) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) :
    ∃ (runs : List (Fin 6)) (pre : List Bool) (bit : Bool),
      counterWord runs = ([true, true, false] ++ word).reverse ∧ word = pre ++ [bit] ∧
      rawSystem.Block
        ⟨79, head, ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
          word ++ false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
        (word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length))
        ⟨Selector.entryState r,
          Move.right.apply (head + (word.length : Int) + 3 - (counterTime runs : Int) + (pre.length : Int)),
          Grammar.finalTape pre bit write .right
            (false :: true :: true :: (List.replicate 7 false ++ left))
            (true :: false :: (List.replicate gap true ++ true :: tail))⟩ [] := by
  obtain ⟨runs, hword⟩ := named_path_codec hpath
  obtain ⟨pre, bit, hw, hbit⟩ := named_increment_ending r write hpath rfl
  obtain ⟨pre', bit', hw', hb⟩ := Preparation.follow_named hpath rfl head
    (false :: true :: true :: (List.replicate 6 false ++ false :: left))
    (false :: false :: (List.replicate gap false ++ true :: tail))
  have hbit' : write = bit' := by
    have h := congrArg List.reverse (hw.symm.trans hw')
    simp only [List.reverse_append, List.reverse_cons, List.reverse_nil, List.nil_append,
      List.singleton_append, List.cons.injEq] at h
    exact hbit.trans h.1
  have hl : write :: (pre'.reverse ++ false :: true :: true :: (List.replicate 6 false ++ false :: left)) =
      counterWord runs ++ List.replicate 6 false ++ false :: left := by
    rw [hword, hw', hbit']
    simp [List.reverse_append, List.reverse_cons, List.append_assoc]
  have hroot : Grammar.nodes[(157 : Fin 158)].state = 79 := by decide
  rw [hroot] at hb
  have hh : head + (pre'.length : Int) + 1 = head + (word.length : Int) := by
    rw [hw']; simp; omega
  have hb' : rawSystem.Block
      ⟨79, head, ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ word.length
      ⟨Selector.entryState r, head + (word.length : Int),
        ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
          false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ [] := by
    simpa only [Grammar.finalTape, moveRight, Move.apply, hh, hl, Option.toList_none,
      List.drop_succ_cons, List.drop_zero] using hb
  obtain ⟨pre2, bit2, hw2, hback⟩ := prepared_redispatch r gap runs word write hword hpath
    (head + (word.length : Int)) left tail
  exact ⟨runs, pre2, bit2, hword, hw2, by simpa using hb'.trans rawSystem hback⟩

/-- A checked named path, its clean-gap preparation, and redispatch compose
into one exact positive silent segment on the selected 236-state table. -/
theorem physical_root_prepare_redispatch (r : Fin 9) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".inc") (Selector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ c) :
    ∃ (runs : List (Fin 6)) (pre : List Bool) (bit : Bool) (finish : Config 237),
      counterWord runs = ([true, true, false] ++ word).reverse ∧ word = pre ++ [bit] ∧
      (machineWordSystem raw rawLabels).Block c
        (word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)) finish [] ∧
      Related ⟨Selector.entryState r,
        Move.right.apply (head + (word.length : Int) + 3 - (counterTime runs : Int) + (pre.length : Int)),
        Grammar.finalTape pre bit write .right
          (false :: true :: true :: (List.replicate 7 false ++ left))
          (true :: false :: (List.replicate gap true ++ true :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length))
        (mapConfig finish) [] ∧
      0 < word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length) := by
  obtain ⟨runs, pre, bit, hw, hp, hb⟩ := root_prepare_redispatch r gap word write hpath head left tail
  obtain ⟨finish, hraw, hfinal⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨runs, pre, bit, finish, hw, hp, hraw, hfinal, BootstrapScan.mapped_block hraw, by omega⟩

example : rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false, false, false, false, true]⟩⟩ 46
    ⟨58, 6, ⟨[false, true, true, false, false, false, false, true, true,
      false, false, false, false, false, false, false], [true, false, true, true, true]⟩⟩ [] := by
  constructor <;> decide

example : ¬ rawSystem.Block
    ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
      [false, false, false, true, true, false, false, false, false, false, true]⟩⟩ 45
    ⟨58, 6, ⟨[false, true, true, false, false, false, false, true, true,
      false, false, false, false, false, false, false], [true, false, true, true, true]⟩⟩ [] := by
  intro h
  have bad : rawSystem.advance
      ⟨79, 0, ⟨[false, true, true, false, false, false, false, false, false, false],
        [false, false, false, true, true, false, false, false, false, false, true]⟩⟩ 45 ≠
      ⟨58, 6, ⟨[false, true, true, false, false, false, false, true, true,
        false, false, false, false, false, false, false], [true, false, true, true, true]⟩⟩ := by decide
  exact bad h.endpoint
end PASoundness.M236.Redispatch
