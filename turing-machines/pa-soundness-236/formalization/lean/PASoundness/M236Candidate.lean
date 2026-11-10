import PASoundness.M236ContinueCoverage
/-! Extract the actual reflected continue-control candidates. -/
set_option maxRecDepth 8192
set_option maxHeartbeats 0
namespace PASoundness.M236.Continue
open Shared.Beeping Shared.Beeping.Machines
open PASoundness.M236.FiniteTape PASoundness.M236.UnaryShift PASoundness.M236.UnaryAnchor

theorem candidate1_data (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.1" 72 false .left none)) :
    ∃ first runs bit tail, candidate1 pre = some (first, runs, bit, tail) ∧
      stack pre = List.replicate first false ++ true :: counterWord runs ∧
      counterPush runs (suffix1 first) = true :: bit :: tail := by
  have hm := Grammar.every_leaf_path _ (Redispatch.named_leaf_path hpath)
  have hc := (List.all_eq_true.mp coverage_checked) (pre ++ [last]) hm
  have hn := pathName_named hpath
  simp only [edgeName] at hn
  unfold coverageOK at hc
  rw [hn] at hc
  simp only [List.dropLast_append_cons, List.dropLast_singleton, List.append_nil] at hc
  unfold check1 at hc
  cases hcan : candidate1 pre with
  | none => simp [hcan] at hc
  | some p =>
    rcases p with ⟨first, runs, bit, tail⟩
    simp only [hcan] at hc
    exact ⟨first, runs, bit, tail, rfl, of_decide_eq_true hc⟩

theorem candidate2_data (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.2" 73 false .left none)) :
    ∃ first second runs bit tail, candidate2 pre = some (first, second, runs, bit, tail) ∧
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
  unfold check2 at hc
  cases hcan : candidate2 pre with
  | none => simp [hcan] at hc
  | some p =>
    rcases p with ⟨first, second, runs, bit, tail⟩
    simp only [hcan] at hc
    exact ⟨first, second, runs, bit, tail, rfl, of_decide_eq_true hc⟩

theorem candidate3_data (pre : List Bool) (last : Bool)
    (hpath : Preparation.NamedPath Grammar.nodes 157 (pre ++ [last])
      (.leaf "_continue.3" 74 false .left none)) :
    ∃ first second third runs bit tail, candidate3 pre = some (first, second, third, runs, bit, tail) ∧
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
  unfold check3 at hc
  cases hcan : candidate3 pre with
  | none => simp [hcan] at hc
  | some p =>
    rcases p with ⟨first, second, third, runs, bit, tail⟩
    simp only [hcan] at hc
    exact ⟨first, second, third, runs, bit, tail, rfl, of_decide_eq_true hc⟩
end PASoundness.M236.Continue
