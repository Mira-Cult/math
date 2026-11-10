import PASoundness.M236BreakLeaf
/-! Reflected stack coverage for the literal named break occurrences. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Break
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def base1 (first scratch : Nat) : Nat := scratch + 1 + (first + 1)
def base3 (first second third scratch : Nat) : Nat := scratch + 1 + (third + 1 + (second + 1 + (first + 1)))

def candidate1 (pre : List Bool) : Option (Nat × Nat × List (Fin 6) × Bool × List Bool) := do
  let (first, rem1) ← Control.pop (Continue.stack pre)
  let (scratch, rem2) ← Control.pop rem1
  let runs ← Grammar.encodeRuns rem2 0
  match counterPush runs (List.replicate (base1 first scratch) false) with
  | true :: bit :: tail => some (first, scratch, runs, bit, tail)
  | _ => none

def candidate3 (pre : List Bool) : Option (Nat × Nat × Nat × Nat × List (Fin 6) × Bool × List Bool) := do
  let (first, rem1) ← Control.pop (Continue.stack pre)
  let (second, rem2) ← Control.pop rem1
  let (third, rem3) ← Control.pop rem2
  let (scratch, rem4) ← Control.pop rem3
  let runs ← Grammar.encodeRuns rem4 0
  match counterPush runs (List.replicate (base3 first second third scratch) false) with
  | true :: bit :: tail => some (first, second, third, scratch, runs, bit, tail)
  | _ => none

def check1 (pre : List Bool) : Bool :=
  match candidate1 pre with
  | none => false
  | some (first, scratch, runs, bit, tail) => decide
      (Continue.stack pre = List.replicate first true ++ false ::
        (List.replicate scratch true ++ false :: counterWord runs) ∧
       counterPush runs (List.replicate (base1 first scratch) false) = true :: bit :: tail)

def check3 (pre : List Bool) : Bool :=
  match candidate3 pre with
  | none => false
  | some (first, second, third, scratch, runs, bit, tail) => decide
      (Continue.stack pre = List.replicate first true ++ false ::
        (List.replicate second true ++ false :: (List.replicate third true ++ false ::
          (List.replicate scratch true ++ false :: counterWord runs))) ∧
       counterPush runs (List.replicate (base3 first second third scratch) false) = true :: bit :: tail)

def coverageOK (word : List Bool) : Bool :=
  match Continue.pathName 157 word with
  | some "_break.1" => check1 word.dropLast
  | some "_break.3" => check3 word.dropLast
  | _ => true

def occurrenceCount (name : String) : Nat :=
  (Grammar.completePaths.filter (fun word => Continue.pathName 157 word == some name)).length

theorem occurrence_counts : occurrenceCount "_break.1" = 42 ∧ occurrenceCount "_break.3" = 10 := by decide

/-- The exact finite grammar checks both break levels, including sentinel cases. -/
theorem coverage_checked : Grammar.completePaths.all coverageOK = true := by decide
theorem candidate1_data (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none)) :
    ∃ first scratch runs bit tail, candidate1 pre = some (first, scratch, runs, bit, tail) ∧
      Continue.stack pre = List.replicate first true ++ false ::
        (List.replicate scratch true ++ false :: counterWord runs) ∧
      counterPush runs (List.replicate (base1 first scratch) false) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [last]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  unfold coverageOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hc
  unfold check1 at hc
  cases hcan : candidate1 pre with
  | none => simp [hcan] at hc
  | some p =>
    rcases p with ⟨first, scratch, runs, bit, tail⟩
    simp only [hcan] at hc
    exact ⟨first, scratch, runs, bit, tail, rfl, of_decide_eq_true hc⟩

theorem candidate3_data (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none)) :
    ∃ first second third scratch runs bit tail,
      candidate3 pre = some (first, second, third, scratch, runs, bit, tail) ∧
      Continue.stack pre = List.replicate first true ++ false ::
        (List.replicate second true ++ false :: (List.replicate third true ++ false ::
          (List.replicate scratch true ++ false :: counterWord runs))) ∧
      counterPush runs (List.replicate (base3 first second third scratch) false) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [last]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  unfold coverageOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hc
  unfold check3 at hc
  cases hcan : candidate3 pre with
  | none => simp [hcan] at hc
  | some p =>
    rcases p with ⟨first, second, third, scratch, runs, bit, tail⟩
    simp only [hcan] at hc
    exact ⟨first, second, third, scratch, runs, bit, tail, rfl, of_decide_eq_true hc⟩

/-- Every named break.1 path returns silently from the canonical prepared root
with arbitrary finite zero gap and the complete trailing tape. -/
theorem physical_covered_break1 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.1" 69 false .left none))
    (gap : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual : List Bool) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          residual ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, scratch, runs, bit, residual, hcan, hs, hc⟩ := candidate1_data pre last hpath
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first true ++ false :: (List.replicate scratch true ++ false ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left)) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [Continue.stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs
      (List.replicate (scratch + 1 + (first + 1 + gap)) false ++ true :: false :: tail) =
      true :: bit :: (residual ++ (List.replicate gap false ++ true :: false :: tail)) := by
    have hn : scratch + 1 + (first + 1 + gap) = base1 first scratch + gap := by dsimp [base1]; omega
    rw [hn, ← List.replicate_append_replicate, List.append_assoc]
    have h := counterPush_append runs (List.replicate (base1 first scratch) false)
      (List.replicate gap false ++ true :: false :: tail)
    rw [hc] at h
    exact h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_break1_to_root pre last hpath first scratch gap runs bit
    (residual ++ (List.replicate gap false ++ true :: false :: tail)) head
    (false :: true :: true :: (List.replicate 7 false ++ left)) left tail c hstack hroot hrel
  exact ⟨_, _, residual, finish, by omega, hp, hr, hq⟩

/-- Every named break.3 path returns silently from the canonical prepared root
with arbitrary finite zero gap and the complete trailing tape. -/
theorem physical_covered_break3 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_break.3" 71 false .left none))
    (gap : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [last]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual : List Bool) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          residual ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, second, third, scratch, runs, bit, residual, hcan, hs, hc⟩ := candidate3_data pre last hpath
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first true ++ false :: (List.replicate second true ++ false ::
        (List.replicate third true ++ false :: (List.replicate scratch true ++ false ::
          (counterWord runs ++ List.replicate 6 false ++ false :: left)))) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [Continue.stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs
      (List.replicate (scratch + 1 + (third + 1 + (second + 1 + (first + 1 + gap)))) false ++
        true :: false :: tail) = true :: bit :: (residual ++ (List.replicate gap false ++ true :: false :: tail)) := by
    have hn : scratch + 1 + (third + 1 + (second + 1 + (first + 1 + gap))) =
        base3 first second third scratch + gap := by dsimp [base3]; omega
    rw [hn, ← List.replicate_append_replicate, List.append_assoc]
    have h := counterPush_append runs (List.replicate (base3 first second third scratch) false)
      (List.replicate gap false ++ true :: false :: tail)
    rw [hc] at h
    exact h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_break3_to_root pre last hpath
    first second third scratch gap runs bit (residual ++ (List.replicate gap false ++ true :: false :: tail)) head
    (false :: true :: true :: (List.replicate 7 false ++ left)) left tail c hstack hroot hrel
  exact ⟨_, _, residual, finish, by omega, hp, hr, hq⟩
end PASoundness.M236.Break
