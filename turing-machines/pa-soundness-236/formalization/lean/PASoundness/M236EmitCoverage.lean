import PASoundness.M236EmitCleanup
/-! Reflected stack coverage for both physical fused-output row forms. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Emit
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def continueCandidate (pre : List Bool) : Option (Nat × List (Fin 6) × Bool × List Bool) := do
  let (first, rem) ← Continue.popOne (Continue.stack pre)
  let runs ← Grammar.encodeRuns rem 0
  match counterPush runs (List.replicate first false ++ [true]) with
  | true :: bit :: tail => some (first, runs, bit, tail)
  | _ => none

def cleanupCandidate (pre : List Bool) : Option (Nat × List (Fin 6) × Bool × List Bool) := do
  let (scratch, rem) ← Control.pop (Continue.stack pre)
  let runs ← Grammar.encodeRuns rem 0
  match counterPush runs (List.replicate (scratch + 1) false) with
  | true :: bit :: tail => some (scratch, runs, bit, tail)
  | _ => none

def checkContinue (pre : List Bool) : Bool :=
  match continueCandidate pre with
  | none => false
  | some (first, runs, bit, tail) => decide
      (Continue.stack pre = List.replicate first false ++ true :: counterWord runs ∧
       counterPush runs (List.replicate first false ++ [true]) = true :: bit :: tail)

def checkCleanup (pre : List Bool) : Bool :=
  match cleanupCandidate pre with
  | none => false
  | some (scratch, runs, bit, tail) => decide
      (Continue.stack pre = List.replicate scratch true ++ false :: counterWord runs ∧
       counterPush runs (List.replicate (scratch + 1) false) = true :: bit :: tail)

def coverageOK (word : List Bool) : Bool :=
  match Continue.pathName 157 word with
  | some "emit.0" | some "emit.1" =>
    match word.reverse with
    | false :: _ => checkContinue word.dropLast
    | true :: _ => checkCleanup word.dropLast
    | _ => false
  | _ => true

def occurrenceCount (name : String) (last : Bool) : Nat :=
  (Grammar.completePaths.filter (fun word => Continue.pathName 157 word == some name &&
    word.getLast? == some last)).length

/-- The literal graph has nineteen continue-style outputs and one cleanup-style output. -/
theorem occurrence_counts : occurrenceCount "emit.0" false = 9 ∧ occurrenceCount "emit.1" false = 10 ∧
    occurrenceCount "emit.0" true = 1 ∧ occurrenceCount "emit.1" true = 0 := by decide

/-- Every named fused output occurrence has the checked return stack. -/
theorem coverage_checked : Grammar.completePaths.all coverageOK = true := by decide

theorem continue_data (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [false])
      (.leaf (emitName b) 72 true .left (some b))) :
    ∃ first runs bit tail, continueCandidate pre = some (first, runs, bit, tail) ∧
      Continue.stack pre = List.replicate first false ++ true :: counterWord runs ∧
      counterPush runs (List.replicate first false ++ [true]) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [false]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  cases b <;> simp [coverageOK, emitName, hn, List.reverse_append] at hc
  all_goals
    unfold checkContinue at hc
    cases hcan : continueCandidate pre with
    | none => simp [hcan] at hc
    | some p =>
      rcases p with ⟨first, runs, bit, tail⟩
      simp only [hcan] at hc
      exact ⟨first, runs, bit, tail, rfl, of_decide_eq_true hc⟩

theorem cleanup_data (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [true])
      (.leaf (emitName b) 68 false .left (some b))) :
    ∃ scratch runs bit tail, cleanupCandidate pre = some (scratch, runs, bit, tail) ∧
      Continue.stack pre = List.replicate scratch true ++ false :: counterWord runs ∧
      counterPush runs (List.replicate (scratch + 1) false) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [true]) hm
  have hn := Continue.pathName_named hpath
  simp only [Continue.edgeName] at hn
  cases b <;> simp [coverageOK, emitName, hn, List.reverse_append] at hc
  all_goals
    unfold checkCleanup at hc
    cases hcan : cleanupCandidate pre with
    | none => simp [hcan] at hc
    | some p =>
      rcases p with ⟨scratch, runs, bit, tail⟩
      simp only [hcan] at hc
      exact ⟨scratch, runs, bit, tail, rfl, of_decide_eq_true hc⟩
/-- Every continue-style marked occurrence returns from the canonical prepared
root tape, preserving exactly its emitted bit and arbitrary finite gap. -/
theorem physical_covered_continue (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [false])
      (.leaf (emitName b) 72 true .left (some b)))
    (gap : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [false]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual : List Bool) (finish : Config 237)
      (first : Nat) (runs : List (Fin 6)) (bit : Bool),
      continueCandidate pre = some (first, runs, bit, residual) ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [b] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          residual ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [b] := by
  obtain ⟨first, runs, bit, residual, hcan, hs, hc⟩ := continue_data b pre hpath
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [Continue.stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs
      (List.replicate first false ++ true :: (List.replicate gap false ++ true :: false :: tail)) =
      true :: bit :: (residual ++ (List.replicate gap false ++ true :: false :: tail)) := by
    have h := counterPush_append runs (List.replicate first false ++ [true])
      (List.replicate gap false ++ true :: false :: tail)
    rw [hc] at h
    simpa [List.append_assoc] using h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_emit_to_root b pre false hpath first runs bit
    (residual ++ (List.replicate gap false ++ true :: false :: tail)) head
    (false :: true :: true :: (List.replicate 7 false ++ left)) left
    (List.replicate gap false ++ true :: false :: tail) c hstack hroot hrel
  exact ⟨_, _, residual, finish, first, runs, bit, hcan, by omega, hp, hr, hq⟩

/-- Every cleanup-style marked occurrence returns from the canonical prepared
root tape, preserving exactly its emitted bit and arbitrary finite gap. -/
theorem physical_covered_cleanup (b : Bool) (pre : List Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [true])
      (.leaf (emitName b) 68 false .left (some b)))
    (gap : Nat) (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left),
        (pre ++ [true]) ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual : List Bool) (finish : Config 237)
      (scratch : Nat) (runs : List (Fin 6)) (bit : Bool),
      cleanupCandidate pre = some (scratch, runs, bit, residual) ∧
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [b] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left),
          residual ++ (List.replicate gap false ++ true :: false :: tail)⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [b] := by
  obtain ⟨scratch, runs, bit, residual, hcan, hs, hc⟩ := cleanup_data b pre hpath
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate scratch true ++ false ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [Continue.stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs
      (List.replicate (scratch + 1 + gap) false ++ true :: false :: tail) =
      true :: bit :: (residual ++ (List.replicate gap false ++ true :: false :: tail)) := by
    rw [← List.replicate_append_replicate, List.append_assoc]
    have h := counterPush_append runs (List.replicate (scratch + 1) false)
      (List.replicate gap false ++ true :: false :: tail)
    rw [hc] at h
    exact h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_emit_cleanup_to_root b pre true hpath scratch gap runs bit
    (residual ++ (List.replicate gap false ++ true :: false :: tail)) head
    (false :: true :: true :: (List.replicate 7 false ++ left)) left tail c hstack hroot hrel
  exact ⟨_, _, residual, finish, scratch, runs, bit, hcan, by omega, hp, hr, hq⟩
end PASoundness.M236.Emit
