import Sude.PermutationConditionalLaw
import Mathlib.Probability.UniformOn

/-! Uniform finite probability spaces for the permutation exposure. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

local instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- The uniform probability space of whole permutations. -/
def uniformPermutation (n : ℕ) : Measure (Equiv.Perm (Fin n)) :=
  uniformOn (Set.univ : Set (Equiv.Perm (Fin n)))

theorem uniformPermutation_isProbability (n : ℕ) :
    IsProbabilityMeasure (uniformPermutation n) := by
  unfold uniformPermutation
  infer_instance

/-- The uniform measure on a realizable revealed history. -/
def permutationHistoryMeasure {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) : Measure (Equiv.Perm (Fin n)) :=
  uniformOn (permutationHistory positions reference : Set (Equiv.Perm (Fin n)))

theorem permutationHistoryMeasure_isProbability {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) :
    IsProbabilityMeasure (permutationHistoryMeasure positions reference) := by
  apply isProbabilityMeasure_uniformOn
  · exact (permutationHistory positions reference).finite_toSet
  · exact ⟨reference, by simp [permutationHistory]⟩

/-- The history measure is conditioning the original uniform measure, not
an independent resampling of the previously revealed coordinates. -/
theorem permutationHistoryMeasure_eq_cond {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) :
    permutationHistoryMeasure positions reference =
      (uniformPermutation n)[| (permutationHistory positions reference : Set (Equiv.Perm (Fin n)))] := by
  unfold permutationHistoryMeasure uniformPermutation uniformOn
  rw [cond_cond_eq_cond_inter (MeasurableSet.univ) (by measurability)]
  simp

/-- The conditional event measure is exactly the counted event fiber divided
by the number of completions of the observed history. -/
theorem permutationHistoryMeasure_event {n : ℕ} (positions targets : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) :
    permutationHistoryMeasure positions reference
        (permutationHistoryEvent positions targets reference i : Set (Equiv.Perm (Fin n))) =
      ((permutationHistoryEvent positions targets reference i).card : ENNReal) /
        ((permutationHistory positions reference).card : ENNReal) := by
  unfold permutationHistoryMeasure
  rw [uniformOn_apply_finset]
  have hsub : permutationHistoryEvent positions targets reference i ⊆
      permutationHistory positions reference := Finset.filter_subset _ _
  rw [Finset.inter_eq_right.mpr hsub]

/-- The conditional probability of any event is the fraction of unused
values in that event, expressed without division. -/
theorem permutationHistoryMeasure_event_uniform {n : ℕ} (positions targets : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions) :
    ((n - positions.card : ℕ) : ENNReal) *
      permutationHistoryMeasure positions reference
        (permutationHistoryEvent positions targets reference i : Set (Equiv.Perm (Fin n))) =
      ((targets \ positions.image reference).card : ENNReal) := by
  have hpos : 0 < (permutationHistory positions reference).card := by
    apply Finset.card_pos.mpr
    exact ⟨reference, by simp [permutationHistory]⟩
  have hzero : ((permutationHistory positions reference).card : ENNReal) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hpos)
  have htop : ((permutationHistory positions reference).card : ENNReal) ≠ ⊤ :=
    ENNReal.natCast_ne_top _
  rw [permutationHistoryMeasure_event, ← mul_div_assoc, ← Nat.cast_mul,
    permutationHistory_event_uniform_all positions targets reference i hi, Nat.cast_mul,
    ENNReal.mul_div_cancel_right hzero htop]

end
end Sude
