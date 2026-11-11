import Sude.PermutationMomentTower
import Sude.PermutationExposureLast

/-! Weighted finite-permutation moment argument. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance weightedMGFPermMeasurable (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- A weighted sum of values sampled by a whole permutation. -/
def permutationWeightedSum {n : ℕ} (slots : Finset (Fin n)) (weights values : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : ℝ := ∑ j ∈ slots, weights j * values (p j)

/-- Center by the exact conditional mean on the previously exposed history. -/
def permutationWeightedCentered {n : ℕ} (positions slots : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (weights values : Fin n → ℝ)
    (p : Equiv.Perm (Fin n)) : ℝ :=
  permutationWeightedSum slots weights values p -
    (permutationHistoryMeasure positions reference)[permutationWeightedSum slots weights values]

/-- Sum of the one-slot source variance proxies. -/
def permutationWeightedProxy {n : ℕ} (slots : Finset (Fin n)) (weights : Fin n → ℝ)
    (lo upper : ℝ) : NNReal :=
  ∑ j ∈ slots, (‖weights j * upper - weights j * lo‖₊ / 2) ^ 2

/-- Exact telescoping into the current reveal and the centered future sum. -/
theorem permutationWeightedCentered_decompose {n : ℕ} (positions slots : Finset (Fin n))
    (reference p : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∈ slots)
    (weights values : Fin n → ℝ) :
    permutationWeightedCentered positions slots reference weights values p =
      permutationRevealIncrement positions slots reference i weights values p +
        permutationWeightedCentered (insert i positions) (slots.erase i) p weights values p := by
  unfold permutationWeightedCentered permutationWeightedSum permutationRevealIncrement
  have hsum := Finset.add_sum_erase slots (fun j => weights j * values (p j)) hi
  rw [← hsum]
  ring

/-- Two references in the same next fiber give the same extended-history
measure. -/
theorem permutationHistoryMeasure_eq_of_next {n : ℕ} (positions : Finset (Fin n))
    (reference p q : Equiv.Perm (Fin n)) (i a : Fin n)
    (hp : p ∈ permutationHistoryNext positions reference i a)
    (hq : q ∈ permutationHistoryNext positions reference i a) :
    permutationHistoryMeasure (insert i positions) p =
      permutationHistoryMeasure (insert i positions) q := by
  have hp' := permutationHistoryNext_eq_insert positions reference p i a hp
  have hq' := permutationHistoryNext_eq_insert positions reference q i a hq
  unfold permutationHistoryMeasure
  rw [← hp', ← hq']

/-- On a next-value fiber, the future centered sum may use any reference
permutation in that fiber. -/
theorem permutationWeighted_future_ae {n : ℕ} (positions slots : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (a : {a // a ∈ (positions.image reference)ᶜ}) (weights values : Fin n → ℝ) :
    let e := permutationHistoryExtension positions reference i hi a
    let ν := permutationHistoryMeasure (insert i positions) e
    (fun p => permutationWeightedCentered (insert i positions) slots p weights values p) =ᵐ[ν]
      permutationWeightedCentered (insert i positions) slots e weights values := by
  let e := permutationHistoryExtension positions reference i hi a
  let ν := permutationHistoryMeasure (insert i positions) e
  have he : e ∈ permutationHistoryNext positions reference i a.val :=
    permutationHistoryExtension_mem positions reference i hi a
  have hset := permutationHistoryNext_eq_insert positions reference e i a.val he
  have hmem : ∀ᵐ p ∂ν, p ∈ permutationHistory (insert i positions) e := by
    change ∀ᵐ p ∂Measure.count[| (permutationHistory (insert i positions) e : Set (Equiv.Perm (Fin n)))],
      p ∈ permutationHistory (insert i positions) e
    exact ae_cond_mem (by measurability)
  filter_upwards [hmem] with p hp
  have hp' : p ∈ permutationHistoryNext positions reference i a.val := by
    rw [hset]
    exact hp
  have hμ := permutationHistoryMeasure_eq_of_next positions reference p e i a.val hp' he
  unfold permutationWeightedCentered
  rw [hμ]

end
end Sude
