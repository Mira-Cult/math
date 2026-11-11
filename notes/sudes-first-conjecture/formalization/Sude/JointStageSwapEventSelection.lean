import Sude.FiniteUniformStageMeasure
import Mathlib.MeasureTheory.Measure.Prod

/-! Select one joint stage assignment and swap vector avoiding a supplied
midpoint failure and two stage-only failures. No independence between the
midpoint and gap events, and no physical or witness construction, is assumed. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory

local instance jointEventPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- A probability budget on a product space yields one outcome avoiding a
joint bad event and both first-coordinate bad events. -/
theorem product_probability_three_events_select {α β : Type*}
    [MeasurableSpace α] [MeasurableSpace β]
    (μ : Measure α) (ν : Measure β) [IsProbabilityMeasure μ] [IsProbabilityMeasure ν]
    (midBad : Set (α × β)) (gapBad : Bool → Set α)
    (hmid : (μ.prod ν).real midBad ≤ (1/2 : ℝ))
    (hgap : ∀ side, μ.real (gapBad side) ≤ (1/8 : ℝ)) :
    ∃ a b, (a,b) ∉ midBad ∧ a ∉ gapBad true ∧ a ∉ gapBad false := by
  classical
  have hlift (side : Bool) : (μ.prod ν).real (Prod.fst ⁻¹' gapBad side) = μ.real (gapBad side) := by
    have heq : Prod.fst ⁻¹' gapBad side = gapBad side ×ˢ (Set.univ : Set β) := by
      ext x
      simp
    rw [heq, measureReal_prod_prod]
    simp
  by_contra hnone
  have hcover : midBad ∪ (Prod.fst ⁻¹' gapBad true) ∪ (Prod.fst ⁻¹' gapBad false) = Set.univ := by
    ext x
    simp only [Set.mem_union, Set.mem_preimage, Set.mem_univ, iff_true]
    by_contra h
    push_neg at h
    exact hnone ⟨x.1,x.2,h.1.1,h.1.2,h.2⟩
  have hu := measureReal_union_le (μ := μ.prod ν) (midBad ∪ (Prod.fst ⁻¹' gapBad true)) (Prod.fst ⁻¹' gapBad false)
  have hv := measureReal_union_le (μ := μ.prod ν) midBad (Prod.fst ⁻¹' gapBad true)
  rw [hcover] at hu
  rw [hlift true] at hv
  rw [hlift false] at hu
  have ht := hgap true
  have hf := hgap false
  have hone : (μ.prod ν).real Set.univ = 1 := by simp
  rw [hone] at hu
  linarith

/-- The same selection principle on the actual stage-permutation and fair
swap spaces. The midpoint event is measured on their joint product, while
both gap events depend only on the stage assignment. -/
theorem stage_swap_three_events_select {W B : ℕ}
    (midBad : Set ((Fin W → Equiv.Perm (Fin B)) × ((Fin W × Fin B) → Bool)))
    (gapBad : Bool → Set (Fin W → Equiv.Perm (Fin B)))
    (hmid : ((stagePermutationMeasure W B).prod
      (uniformOn (Set.univ : Set ((Fin W × Fin B) → Bool)))).real midBad ≤ (1/2 : ℝ))
    (hgap : ∀ side, (stagePermutationMeasure W B).real (gapBad side) ≤ (1/8 : ℝ)) :
    ∃ π swaps, (π,swaps) ∉ midBad ∧ π ∉ gapBad true ∧ π ∉ gapBad false := by
  let μ := stagePermutationMeasure W B
  let ν := uniformOn (Set.univ : Set ((Fin W × Fin B) → Bool))
  have : IsProbabilityMeasure μ := stagePermutationMeasure_isProbability W B
  have : IsProbabilityMeasure ν := inferInstance
  exact product_probability_three_events_select μ ν midBad gapBad hmid hgap

end
end Sude
