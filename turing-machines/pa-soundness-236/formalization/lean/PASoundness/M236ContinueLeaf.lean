import PASoundness.M236Continue
/-! Named literal continue leaves followed by their physical return. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A known named silent left-moving leaf is followed with its whole tape. -/
theorem physical_named_leaf (name : String) (target : Fin 237) (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf name target false .left none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head, ⟨left, (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c (pre ++ [last]).length finish [] ∧
      Related ⟨target, Move.left.apply (head + (pre.length : Int)),
        Grammar.finalTape pre last false .left left tail⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) (pre ++ [last]).length
        (mapConfig finish) [] ∧ 0 < (pre ++ [last]).length := by
  obtain ⟨pre', last', hw, hb⟩ := Preparation.follow_named hpath rfl head left tail
  have heq : last' :: pre'.reverse = last :: pre.reverse := by
    have hrev := congrArg List.reverse hw
    simpa [List.reverse_append] using hrev.symm
  have hlast : last' = last := (List.cons.inj heq).1
  have hpre : pre' = pre := List.reverse_inj.mp (List.cons.inj heq).2
  subst last'
  subst pre'
  have hroot : Grammar.nodes[(157 : Fin 158)].state = 79 := by decide
  rw [hroot] at hb
  simp only [Option.toList_none] at hb
  obtain ⟨finish, hp, hr, hq⟩ := physical_silent_block _ _ _ hb c hrel
  exact ⟨finish, hp, hr, hq, by simp⟩

/-- A named continue.1 leaf physically returns to the root, under the displayed
stack and root-prefix conditions. -/
theorem physical_named_continue1_to_root (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (first : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (rootLeft left tail : List Bool) (c : Config 237)
    (hstack : pre.reverse ++ rootLeft = List.replicate first false ++ true ::
      (counterWord runs ++ List.replicate 6 false ++ false :: left))
    (hroot : counterPush runs (List.replicate first false ++ false :: tail) = true :: bit :: rootTail)
    (hrel : Related ⟨79, head, ⟨rootLeft, (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((pre ++ [last]).length + (first + 1 + (counterTime runs + 6 + 10))) finish [] ∧
      Related ⟨79, Move.left.apply (head + (pre.length : Int)) - (first : Int) - 1 -
        (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((pre ++ [last]).length + (first + 1 + (counterTime runs + 6 + 10))) (mapConfig finish) [] ∧
      0 < (pre ++ [last]).length ∧ 0 < first + 1 + (counterTime runs + 6 + 10) := by
  obtain ⟨mid, hp, hr, hq, ht⟩ := physical_named_leaf "_continue.1" 72 pre last hpath head rootLeft tail c hrel
  have hr' : Related
      ⟨72, Move.left.apply (head + (pre.length : Int)),
        moveLeft ⟨List.replicate first false ++ true ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left), false :: tail⟩ false⟩ mid := by
    simpa [Grammar.finalTape, hstack, moveLeft] using hr
  obtain ⟨finish, hp', hr'', hq', ht'⟩ := physical_one_to_root first runs bit rootTail
    (Move.left.apply (head + (pre.length : Int))) left tail false mid hroot hr'
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr'',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', ht, ht'⟩
/-- A named continue.2 leaf physically returns to the root. -/
theorem physical_named_continue2_to_root (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (first second : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (rootLeft left tail : List Bool) (c : Config 237)
    (hstack : pre.reverse ++ rootLeft = List.replicate first false ++ true ::
      (List.replicate second false ++ true :: (counterWord runs ++ List.replicate 6 false ++ false :: left)))
    (hroot : counterPush runs (List.replicate second false ++ false ::
      (List.replicate first false ++ false :: tail)) = true :: bit :: rootTail)
    (hrel : Related ⟨79, head, ⟨rootLeft, (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((pre ++ [last]).length + ((first + 1) + (second + 1) + (counterTime runs + 6 + 10))) finish [] ∧
      Related ⟨79, Move.left.apply (head + (pre.length : Int)) - (first : Int) - 1 - (second : Int) - 1 -
        (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((pre ++ [last]).length + ((first + 1) + (second + 1) + (counterTime runs + 6 + 10))) (mapConfig finish) [] ∧
      0 < (pre ++ [last]).length ∧ 0 < (first + 1) + (second + 1) + (counterTime runs + 6 + 10) := by
  obtain ⟨mid, hp, hr, hq, ht⟩ := physical_named_leaf "_continue.2" 73 pre last hpath head rootLeft tail c hrel
  have hr' : Related
      ⟨73, Move.left.apply (head + (pre.length : Int)),
        moveLeft ⟨List.replicate first false ++ true ::
          (List.replicate second false ++ true :: (counterWord runs ++ List.replicate 6 false ++ false :: left)),
          false :: tail⟩ false⟩ mid := by
    simpa [Grammar.finalTape, hstack, moveLeft] using hr
  obtain ⟨finish, hp', hr'', hq', ht'⟩ := physical_two_to_root first second runs bit rootTail
    (Move.left.apply (head + (pre.length : Int))) left tail false mid hroot hr'
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr'',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', ht, ht'⟩

/-- A named continue.3 leaf physically returns to the root. -/
theorem physical_named_continue3_to_root (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (first second third : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (rootLeft left tail : List Bool) (c : Config 237)
    (hstack : pre.reverse ++ rootLeft = List.replicate first false ++ true ::
      (List.replicate second false ++ true :: (List.replicate third false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left))))
    (hroot : counterPush runs (List.replicate third false ++ false ::
      (List.replicate second false ++ false :: (List.replicate first false ++ false :: tail))) =
      true :: bit :: rootTail)
    (hrel : Related ⟨79, head, ⟨rootLeft, (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((pre ++ [last]).length + ((first + 1) + ((second + 1) + (third + 1)) +
          (counterTime runs + 6 + 10))) finish [] ∧
      Related ⟨79, Move.left.apply (head + (pre.length : Int)) - (first : Int) - 1 - (second : Int) - 1 -
        (third : Int) - 1 - (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((pre ++ [last]).length + ((first + 1) + ((second + 1) + (third + 1)) +
          (counterTime runs + 6 + 10))) (mapConfig finish) [] ∧
      0 < (pre ++ [last]).length ∧ 0 < (first + 1) + ((second + 1) + (third + 1)) +
        (counterTime runs + 6 + 10) := by
  obtain ⟨mid, hp, hr, hq, ht⟩ := physical_named_leaf "_continue.3" 74 pre last hpath head rootLeft tail c hrel
  have hr' : Related
      ⟨74, Move.left.apply (head + (pre.length : Int)),
        moveLeft ⟨List.replicate first false ++ true ::
          (List.replicate second false ++ true :: (List.replicate third false ++ true ::
            (counterWord runs ++ List.replicate 6 false ++ false :: left))), false :: tail⟩ false⟩ mid := by
    simpa [Grammar.finalTape, hstack, moveLeft] using hr
  obtain ⟨finish, hp', hr'', hq', ht'⟩ := physical_three_to_root first second third runs bit rootTail
    (Move.left.apply (head + (pre.length : Int))) left tail false mid hroot hr'
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr'',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', ht, ht'⟩
end PASoundness.M236.Continue
