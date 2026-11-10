import PASoundness.M236ContinueLeaf
/-! Reflected stack coverage for every literal named continue occurrence. -/
set_option maxRecDepth 65536
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

def pathName (i : Fin 158) : List Bool → Option String
  | [] => none
  | b :: rest =>
    match Grammar.edge Grammar.nodes i b with
    | .node j => pathName j rest
    | .leaf name _ _ _ _ => if rest.isEmpty then some name else none

def edgeName : Grammar.Edge → Option String
  | .node _ => none
  | .leaf name _ _ _ _ => some name

theorem pathName_named {i : Fin 158} {word : List Bool} {e : Grammar.Edge}
    (h : Preparation.NamedPath Grammar.nodes i word e) : pathName i word = edgeName e := by
  induction h with
  | leaf i b e he hleaf =>
    obtain ⟨name, target, write, move, event, rfl⟩ := hleaf
    simp [pathName, he, edgeName]
  | step i j b tail e he hr ih =>
    simp [pathName, he, ih]

def popOne : List Bool → Option (Nat × List Bool)
  | [] => none
  | true :: rest => some (0, rest)
  | false :: rest => (popOne rest).map (fun (n, tail) => (n + 1, tail))

def stack (pre : List Bool) : List Bool := pre.reverse ++ [false, true, true]

def suffix1 (first : Nat) : List Bool := List.replicate first false ++ [false]
def suffix2 (first second : Nat) : List Bool :=
  List.replicate second false ++ false :: suffix1 first
def suffix3 (first second third : Nat) : List Bool :=
  List.replicate third false ++ false :: suffix2 first second

def candidate1 (pre : List Bool) : Option (Nat × List (Fin 6) × Bool × List Bool) := do
  let (first, rem) ← popOne (stack pre)
  let runs ← Grammar.encodeRuns rem 0
  match counterPush runs (suffix1 first) with
  | true :: bit :: tail => some (first, runs, bit, tail)
  | _ => none

def candidate2 (pre : List Bool) : Option (Nat × Nat × List (Fin 6) × Bool × List Bool) := do
  let (first, rem1) ← popOne (stack pre)
  let (second, rem2) ← popOne rem1
  let runs ← Grammar.encodeRuns rem2 0
  match counterPush runs (suffix2 first second) with
  | true :: bit :: tail => some (first, second, runs, bit, tail)
  | _ => none

def candidate3 (pre : List Bool) : Option (Nat × Nat × Nat × List (Fin 6) × Bool × List Bool) := do
  let (first, rem1) ← popOne (stack pre)
  let (second, rem2) ← popOne rem1
  let (third, rem3) ← popOne rem2
  let runs ← Grammar.encodeRuns rem3 0
  match counterPush runs (suffix3 first second third) with
  | true :: bit :: tail => some (first, second, third, runs, bit, tail)
  | _ => none

def check1 (pre : List Bool) : Bool :=
  match candidate1 pre with
  | none => false
  | some (first, runs, bit, tail) => decide
      (stack pre = List.replicate first false ++ true :: counterWord runs ∧
       counterPush runs (suffix1 first) = true :: bit :: tail)

def check2 (pre : List Bool) : Bool :=
  match candidate2 pre with
  | none => false
  | some (first, second, runs, bit, tail) => decide
      (stack pre = List.replicate first false ++ true ::
        (List.replicate second false ++ true :: counterWord runs) ∧
       counterPush runs (suffix2 first second) = true :: bit :: tail)

def check3 (pre : List Bool) : Bool :=
  match candidate3 pre with
  | none => false
  | some (first, second, third, runs, bit, tail) => decide
      (stack pre = List.replicate first false ++ true ::
        (List.replicate second false ++ true :: (List.replicate third false ++ true :: counterWord runs)) ∧
       counterPush runs (suffix3 first second third) = true :: bit :: tail)

def coverageOK (word : List Bool) : Bool :=
  match pathName 157 word with
  | some "_continue.1" => check1 word.dropLast
  | some "_continue.2" => check2 word.dropLast
  | some "_continue.3" => check3 word.dropLast
  | _ => true

def occurrenceCount (name : String) : Nat :=
  (Grammar.completePaths.filter (fun word => pathName 157 word == some name)).length

/-- The literal graph has these checked numbers of continue occurrences. -/
theorem occurrence_counts : occurrenceCount "_continue.1" = 47 ∧
    occurrenceCount "_continue.2" = 157 ∧ occurrenceCount "_continue.3" = 23 := by decide

/-- The kernel checks all 760 literal leaves, including all continue levels. -/
theorem coverage_checked : Grammar.completePaths.all coverageOK = true := by decide
theorem check1_extract {pre : List Bool} (h : check1 pre = true) :
    ∃ first runs bit tail,
      stack pre = List.replicate first false ++ true :: counterWord runs ∧
      counterPush runs (suffix1 first) = true :: bit :: tail := by
  unfold check1 at h
  cases hc : candidate1 pre with
  | none => simp [hc] at h
  | some p =>
    rcases p with ⟨first, runs, bit, tail⟩
    simp only [hc] at h
    exact ⟨first, runs, bit, tail, of_decide_eq_true h⟩

theorem check2_extract {pre : List Bool} (h : check2 pre = true) :
    ∃ first second runs bit tail,
      stack pre = List.replicate first false ++ true ::
        (List.replicate second false ++ true :: counterWord runs) ∧
      counterPush runs (suffix2 first second) = true :: bit :: tail := by
  unfold check2 at h
  cases hc : candidate2 pre with
  | none => simp [hc] at h
  | some p =>
    rcases p with ⟨first, second, runs, bit, tail⟩
    simp only [hc] at h
    exact ⟨first, second, runs, bit, tail, of_decide_eq_true h⟩

theorem check3_extract {pre : List Bool} (h : check3 pre = true) :
    ∃ first second third runs bit tail,
      stack pre = List.replicate first false ++ true ::
        (List.replicate second false ++ true :: (List.replicate third false ++ true :: counterWord runs)) ∧
      counterPush runs (suffix3 first second third) = true :: bit :: tail := by
  unfold check3 at h
  cases hc : candidate3 pre with
  | none => simp [hc] at h
  | some p =>
    rcases p with ⟨first, second, third, runs, bit, tail⟩
    simp only [hc] at h
    exact ⟨first, second, third, runs, bit, tail, of_decide_eq_true h⟩

theorem coverage1 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none)) :
    ∃ first runs bit tail,
      stack pre = List.replicate first false ++ true :: counterWord runs ∧
      counterPush runs (suffix1 first) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold coverageOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hc
  exact check1_extract hc

theorem coverage2 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none)) :
    ∃ first second runs bit tail,
      stack pre = List.replicate first false ++ true ::
        (List.replicate second false ++ true :: counterWord runs) ∧
      counterPush runs (suffix2 first second) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold coverageOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hc
  exact check2_extract hc

theorem coverage3 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none)) :
    ∃ first second third runs bit tail,
      stack pre = List.replicate first false ++ true ::
        (List.replicate second false ++ true :: (List.replicate third false ++ true :: counterWord runs)) ∧
      counterPush runs (suffix3 first second third) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold coverageOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hc
  exact check3_extract hc
/-- All literal continue.1 occurrences return from a canonical prepared root
tape. No control-stack or root-prefix hypothesis remains. -/
theorem physical_covered_continue1 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual : List Bool) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), residual ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, runs, bit, residual, hs, hc⟩ := coverage1 pre last hpath
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs (List.replicate first false ++ false :: tail) =
      true :: bit :: (residual ++ tail) := by
    have h := counterPush_append runs (suffix1 first) tail
    rw [hc] at h
    simpa [suffix1, List.append_assoc] using h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_continue1_to_root pre last hpath
    first runs bit (residual ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left))
    left tail c hstack hroot hrel
  exact ⟨_, _, residual, finish, by omega, hp, hr, hq⟩
/-- Every literal continue.2 occurrence returns from a canonical prepared root tape. -/
theorem physical_covered_continue2 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual : List Bool) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), residual ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, second, runs, bit, residual, hs, hc⟩ := coverage2 pre last hpath
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first false ++ true :: (List.replicate second false ++ true ::
        (counterWord runs ++ List.replicate 6 false ++ false :: left)) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs (List.replicate second false ++ false ::
      (List.replicate first false ++ false :: tail)) = true :: bit :: (residual ++ tail) := by
    have h := counterPush_append runs (suffix2 first second) tail
    rw [hc] at h
    simpa [suffix1, suffix2, List.append_assoc] using h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_continue2_to_root pre last hpath
    first second runs bit (residual ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left))
    left tail c hstack hroot hrel
  exact ⟨_, _, residual, finish, by omega, hp, hr, hq⟩

/-- Every literal continue.3 occurrence returns from a canonical prepared root tape. -/
theorem physical_covered_continue3 (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none))
    (head : Int) (left tail : List Bool) (c : Config 237)
    (hrel : Related ⟨79, head,
      ⟨false :: true :: true :: (List.replicate 7 false ++ left), (pre ++ [last]) ++ tail⟩⟩ c) :
    ∃ (time : Nat) (endHead : Int) (residual : List Bool) (finish : Config 237),
      0 < time ∧ (machineWordSystem raw rawLabels).Block c time finish [] ∧
      Related ⟨79, endHead,
        ⟨false :: true :: true :: (List.replicate 7 false ++ left), residual ++ tail⟩⟩ finish ∧
      (machineWordSystem machine machineLabels).Block (mapConfig c) time (mapConfig finish) [] := by
  obtain ⟨first, second, third, runs, bit, residual, hs, hc⟩ := coverage3 pre last hpath
  have hstack : pre.reverse ++ (false :: true :: true :: (List.replicate 7 false ++ left)) =
      List.replicate first false ++ true :: (List.replicate second false ++ true ::
        (List.replicate third false ++ true :: (counterWord runs ++ List.replicate 6 false ++ false :: left))) := by
    have h := congrArg (fun xs : List Bool => xs ++ (List.replicate 7 false ++ left)) hs
    simpa [stack, List.append_assoc, List.replicate_succ] using h
  have hroot : counterPush runs (List.replicate third false ++ false ::
      (List.replicate second false ++ false :: (List.replicate first false ++ false :: tail))) =
      true :: bit :: (residual ++ tail) := by
    have h := counterPush_append runs (suffix3 first second third) tail
    rw [hc] at h
    simpa [suffix1, suffix2, suffix3, List.append_assoc] using h
  obtain ⟨finish, hp, hr, hq, ht1, ht2⟩ := physical_named_continue3_to_root pre last hpath
    first second third runs bit (residual ++ tail) head (false :: true :: true :: (List.replicate 7 false ++ left))
    left tail c hstack hroot hrel
  exact ⟨_, _, residual, finish, by omega, hp, hr, hq⟩
end PASoundness.M236.Continue
