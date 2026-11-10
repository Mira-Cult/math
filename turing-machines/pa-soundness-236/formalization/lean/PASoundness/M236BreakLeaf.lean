import PASoundness.M236Break
/-! Named literal break leaves followed by their physical return. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Break
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

/-- A named break.1 leaf returns to the root from the displayed stack and
zero-anchor tape, under the explicit root-prefix condition. -/
theorem physical_named_break1_to_root (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (first scratch gap : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (rootLeft left tail : List Bool) (c : Config 237)
    (hstack : pre.reverse ++ rootLeft = List.replicate first true ++ false ::
      (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left)))
    (hroot : counterPush runs
      (List.replicate (scratch + 1 + (first + 1 + gap)) false ++ true :: false :: tail) =
      true :: bit :: rootTail)
    (hrel : Related ⟨79, head,
      ⟨rootLeft, (pre ++ [last]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((pre ++ [last]).length + ((first + 1) + (3 * scratch + 2 * (first + 1 + gap) + 7) +
          (counterTime runs + 6 + 10))) finish [] ∧
      Related ⟨79, Move.left.apply (head + (pre.length : Int)) - (first : Int) - 1 -
        (scratch : Int) - 1 - (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((pre ++ [last]).length + ((first + 1) + (3 * scratch + 2 * (first + 1 + gap) + 7) +
          (counterTime runs + 6 + 10))) (mapConfig finish) [] ∧
      0 < (pre ++ [last]).length ∧
      0 < (first + 1) + (3 * scratch + 2 * (first + 1 + gap) + 7) + (counterTime runs + 6 + 10) := by
  obtain ⟨mid, hp, hr, hq, ht⟩ := Continue.physical_named_leaf "_break.1" 69 pre last hpath head rootLeft
    (List.replicate gap false ++ true :: false :: tail) c hrel
  have hr' : Related
      ⟨69, Move.left.apply (head + (pre.length : Int)), moveLeft
        ⟨List.replicate first true ++ false ::
          (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left)),
          false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ mid := by
    simpa [Grammar.finalTape, hstack, moveLeft] using hr
  obtain ⟨finish, hp', hr'', hq', ht'⟩ := physical_one_to_root first scratch gap runs bit rootTail
    (Move.left.apply (head + (pre.length : Int))) left tail mid hroot hr'
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr'',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', ht, ht'⟩

/-- A named break.3 leaf returns to the root under the corresponding displayed
stack, zero-anchor tape, and root-prefix conditions. -/
theorem physical_named_break3_to_root (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (first second third scratch gap : Nat) (runs : List (Fin 6)) (bit : Bool) (rootTail : List Bool)
    (head : Int) (rootLeft left tail : List Bool) (c : Config 237)
    (hstack : pre.reverse ++ rootLeft = List.replicate first true ++ false ::
      (List.replicate second true ++ false :: (List.replicate third true ++ false ::
        (List.replicate scratch true ++ false :: (counterWord runs ++ List.replicate 6 false ++ false :: left)))))
    (hroot : counterPush runs
      (List.replicate (scratch + 1 + (third + 1 + (second + 1 + (first + 1 + gap)))) false ++
        true :: false :: tail) = true :: bit :: rootTail)
    (hrel : Related ⟨79, head,
      ⟨rootLeft, (pre ++ [last]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ finish, (machineWordSystem raw rawLabels).Block c
        ((pre ++ [last]).length + (((first + 1) + ((second + 1) + (third + 1))) +
          (3 * scratch + 2 * (third + 1 + (second + 1 + (first + 1 + gap))) + 7) +
          (counterTime runs + 6 + 10))) finish [] ∧
      Related ⟨79, Move.left.apply (head + (pre.length : Int)) - (first : Int) - 1 - (second : Int) - 1 -
        (third : Int) - 1 - (scratch : Int) - 1 - (counterTime runs : Int) - 6 + 10,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), rootTail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c)
        ((pre ++ [last]).length + (((first + 1) + ((second + 1) + (third + 1))) +
          (3 * scratch + 2 * (third + 1 + (second + 1 + (first + 1 + gap))) + 7) +
          (counterTime runs + 6 + 10))) (mapConfig finish) [] ∧
      0 < (pre ++ [last]).length ∧
      0 < ((first + 1) + ((second + 1) + (third + 1))) +
          (3 * scratch + 2 * (third + 1 + (second + 1 + (first + 1 + gap))) + 7) +
          (counterTime runs + 6 + 10) := by
  obtain ⟨mid, hp, hr, hq, ht⟩ := Continue.physical_named_leaf "_break.3" 71 pre last hpath head rootLeft
    (List.replicate gap false ++ true :: false :: tail) c hrel
  have hr' : Related
      ⟨71, Move.left.apply (head + (pre.length : Int)), moveLeft
        ⟨List.replicate first true ++ false :: (List.replicate second true ++ false ::
          (List.replicate third true ++ false :: (List.replicate scratch true ++ false ::
            (counterWord runs ++ List.replicate 6 false ++ false :: left)))),
          false :: (List.replicate gap false ++ true :: false :: tail)⟩ false⟩ mid := by
    simpa [Grammar.finalTape, hstack, moveLeft] using hr
  obtain ⟨finish, hp', hr'', hq', ht'⟩ := physical_three_to_root first second third scratch gap runs bit rootTail
    (Move.left.apply (head + (pre.length : Int))) left tail mid hroot hr'
  exact ⟨finish, by simpa using hp.trans (machineWordSystem raw rawLabels) hp', hr'',
    by simpa using hq.trans (machineWordSystem machine machineLabels) hq', ht, ht'⟩
end PASoundness.M236.Break
