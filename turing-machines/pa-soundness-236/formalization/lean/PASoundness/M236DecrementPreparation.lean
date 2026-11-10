import PASoundness.M236ConcreteIncrement
import PASoundness.M236DecrementSelector
/-! Decrement entries share the checked gap preparation and redispatch.
All root tapes and named paths are explicit; source reachability is separate. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Preparation
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- Positive blocks from configurations with the same first transition agree. -/
theorem same_first_block {C A : Type} (M : WordEventSystem C A) {x y finish : C}
    {word : List A} (n : Nat) (hs : M.step x = M.step y)
    (hb : M.Block x (n + 1) finish word) : M.Block y (n + 1) finish word := by
  have ha : M.advance x 1 = M.advance y 1 := by
    change (M.step x).1 = (M.step y).1
    rw [hs]
  have hw : M.wordFrom x 1 = M.wordFrom y 1 := by
    change [] ++ (M.step x).2 = [] ++ (M.step y).2
    rw [hs]
  have hn : n + 1 = 1 + n := by omega
  constructor
  · rw [hn, M.advance_add, ← ha, ← M.advance_add, ← hn]
    exact hb.endpoint
  · rw [hn, M.wordFrom_add, ← ha, ← hw, ← M.wordFrom_add, ← hn]
    exact hb.output

/-- The increment and decrement entries have the same unprepared first row. -/
theorem decrement_same_first (r : Fin 9) (head : Int) (left tail : List Bool) :
    rawSystem.step ⟨Selector.entryState r, head, ⟨left, false :: tail⟩⟩ =
      rawSystem.step ⟨DecrementSelector.entryState r, head, ⟨left, false :: tail⟩⟩ := by
  have hi := Selector.unprepared_rows r
  have hd := DecrementSelector.unprepared_rows r
  simp [rawSystem, FiniteTape.system, FiniteTape.step, FiniteTape.read, hi.1, hi.2, hd.1, hd.2]

/-- Reuse the existing physical gap-fill proof for a decrement entry. -/
theorem decrement_prepare_gap (r : Fin 9) (gap : Nat) (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨DecrementSelector.entryState r, head,
      ⟨left, false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ (gap + 3)
      ⟨72, head + ((gap + 1 : Nat) : Int),
        moveLeft ⟨List.replicate gap true ++ false :: true :: left, true :: tail⟩ true⟩ [] := by
  have hb := Preparation.prepare_gap r gap head left tail
  have hs := decrement_same_first r head left (false :: (List.replicate gap false ++ true :: tail))
  have ht := same_first_block rawSystem (gap + 2) hs (by simpa [Nat.add_assoc] using hb)
  simpa [Nat.add_assoc] using ht

theorem decrement_prepared_root (r : Fin 9) (gap : Nat) (runs : List (Fin 6)) (word : List Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (head : Int) (left tail : List Bool) :
    rawSystem.Block ⟨DecrementSelector.entryState r, head,
      ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
        false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
      ((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10)
      ⟨79, head + 3 - (counterTime runs : Int),
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          word ++ true :: false :: (List.replicate gap true ++ true :: tail)⟩⟩ [] := by
  have hb := Redispatch.prepared_root r gap runs word hword head left tail
  have hs := decrement_same_first r head (counterWord runs ++ List.replicate 6 false ++ false :: left)
    (false :: (List.replicate gap false ++ true :: tail))
  let n := (gap + 2) + (gap + 2) + (counterTime runs + 6) + 10
  have heq : n + 1 = (gap + 3) + (gap + 2) + (counterTime runs + 6) + 10 := by dsimp [n]; omega
  have ht := same_first_block rawSystem n hs (by rw [heq]; exact hb)
  simpa only [heq] using ht

theorem decrement_prepared_redispatch (r : Fin 9) (gap : Nat) (runs : List (Fin 6))
    (word : List Bool) (write : Bool)
    (hword : counterWord runs = ([true, true, false] ++ word).reverse)
    (hpath : NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) :
    ∃ pre bit, word = pre ++ [bit] ∧
      rawSystem.Block ⟨DecrementSelector.entryState r, head,
        ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
          false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
        (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)
        ⟨DecrementSelector.entryState r,
          Move.right.apply (head + 3 - (counterTime runs : Int) + (pre.length : Int)),
          Grammar.finalTape pre bit write .right
            (false :: true :: true :: (List.replicate 7 false ++ left))
            (true :: false :: (List.replicate gap true ++ true :: tail))⟩ [] := by
  obtain ⟨pre, bit, hw, hb⟩ := follow_named hpath rfl
    (head + 3 - (counterTime runs : Int))
    (false :: true :: true :: (List.replicate 7 false ++ left))
    (true :: false :: (List.replicate gap true ++ true :: tail))
  have hroot : Grammar.nodes[(157 : Fin 158)].state = 79 := by decide
  rw [hroot] at hb
  exact ⟨pre, bit, hw, by simpa using (decrement_prepared_root r gap runs word hword head left tail).trans rawSystem hb⟩

/-- Every named decrement leaf preserves the path bit it reads. -/
theorem decrement_edge_write : ∀ (i : Fin 158) (bit : Bool) (r : Fin 9) (write : Bool),
    Grammar.edge Grammar.nodes i bit =
      .leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none →
    write = bit := by decide

theorem named_decrement_ending (r : Fin 9) (write : Bool) {i : Fin 158}
    {word : List Bool} {e : Grammar.Edge} (h : NamedPath Grammar.nodes i word e)
    (heq : e = .leaf ("3." ++ Selector.registerNames[r] ++ ".decnz")
      (DecrementSelector.entryState r) write .right none) :
    ∃ pre bit, word = pre ++ [bit] ∧ write = bit := by
  induction h with
  | leaf i b e he hl =>
    rw [heq] at he
    exact ⟨[], b, rfl, decrement_edge_write i b r write he⟩
  | step i j b tail e he rest ih =>
    obtain ⟨pre, bit, hw, hbit⟩ := ih heq
    exact ⟨b :: pre, bit, by simp [hw], hbit⟩
/-- Follow a named decrement path, prepare its finite gap, and follow it again. -/
theorem decrement_root_prepare_redispatch (r : Fin 9) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) :
    ∃ (runs : List (Fin 6)) (pre : List Bool) (bit : Bool),
      counterWord runs = ([true, true, false] ++ word).reverse ∧ word = pre ++ [bit] ∧
      rawSystem.Block
        ⟨79, head, ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
          word ++ false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩
        (word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length))
        ⟨DecrementSelector.entryState r,
          Move.right.apply (head + (word.length : Int) + 3 - (counterTime runs : Int) + (pre.length : Int)),
          Grammar.finalTape pre bit write .right
            (false :: true :: true :: (List.replicate 7 false ++ left))
            (true :: false :: (List.replicate gap true ++ true :: tail))⟩ [] := by
  obtain ⟨runs, hword⟩ := Redispatch.named_path_codec hpath
  obtain ⟨pre, bit, hw, hbit⟩ := named_decrement_ending r write hpath rfl
  obtain ⟨pre', bit', hw', hb⟩ := follow_named hpath rfl head
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
      ⟨DecrementSelector.entryState r, head + (word.length : Int),
        ⟨counterWord runs ++ List.replicate 6 false ++ false :: left,
          false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ [] := by
    simpa only [Grammar.finalTape, moveRight, Move.apply, hh, hl, Option.toList_none,
      List.drop_succ_cons, List.drop_zero] using hb
  obtain ⟨pre2, bit2, hw2, hback⟩ := decrement_prepared_redispatch r gap runs word write hword hpath
    (head + (word.length : Int)) left tail
  exact ⟨runs, pre2, bit2, hword, hw2, by simpa using hb'.trans rawSystem hback⟩


/-- Lift the whole preparation and redispatch to the selected quotient. -/
theorem physical_decrement_root_prepare_redispatch (r : Fin 9) (gap : Nat) (word : List Bool) (write : Bool)
    (hpath : NamedPath Grammar.nodes 157 word
      (.leaf ("3." ++ Selector.registerNames[r] ++ ".decnz") (DecrementSelector.entryState r) write .right none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 6 false ++ false :: left),
        word ++ false :: false :: (List.replicate gap false ++ true :: tail)⟩⟩ c) :
    ∃ (runs : List (Fin 6)) (pre : List Bool) (bit : Bool) (finish : Config 237),
      counterWord runs = ([true, true, false] ++ word).reverse ∧ word = pre ++ [bit] ∧
      (machineWordSystem raw rawLabels).Block c
        (word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length)) finish [] ∧
      Related ⟨DecrementSelector.entryState r,
        Move.right.apply (head + (word.length : Int) + 3 - (counterTime runs : Int) + (pre.length : Int)),
        Grammar.finalTape pre bit write .right
          (false :: true :: true :: (List.replicate 7 false ++ left))
          (true :: false :: (List.replicate gap true ++ true :: tail))⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        (word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length))
        (mapConfig finish) [] ∧
      0 < word.length + (((gap + 3) + (gap + 2) + (counterTime runs + 6) + 10) + word.length) := by
  obtain ⟨runs, pre, bit, hw, hp, hb⟩ := decrement_root_prepare_redispatch r gap word write hpath head left tail
  obtain ⟨finish, hraw, hfinal⟩ := BulkSweep.physical_block raw rawLabels _ _ c _ hrel hb
  exact ⟨runs, pre, bit, finish, hw, hp, hraw, hfinal, BootstrapScan.mapped_block hraw, by omega⟩

end PASoundness.M236.Preparation
