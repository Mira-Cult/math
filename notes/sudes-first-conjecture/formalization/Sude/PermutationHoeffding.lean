import Sude.PermutationProbability
import Mathlib.Probability.Moments.SubGaussian

/-! A Hoeffding moment bound on each actual permutation-history fiber. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory

local instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Under each realizable history, a bounded next permutation value,
centered by its actual conditional mean, has Hoeffding's moment bound. -/
theorem permutationHistory_next_subgaussian {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (values : Fin n → ℝ) (c lo upper : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ a, a ∉ positions.image reference → values a ∈ Set.Icc lo upper) :
    let μ := permutationHistoryMeasure positions reference
    HasSubgaussianMGF (fun p => c * values (p i) - μ[fun q => c * values (q i)])
      ((‖c * upper - c * lo‖₊ / 2) ^ 2) μ := by
  let μ := permutationHistoryMeasure positions reference
  let X : Equiv.Perm (Fin n) → ℝ := fun p => c * values (p i)
  have : IsProbabilityMeasure μ := permutationHistoryMeasure_isProbability positions reference
  have hm : AEMeasurable X μ := Measurable.of_discrete.aemeasurable
  have hmem : ∀ᵐ p ∂μ, p ∈ permutationHistory positions reference := by
    change ∀ᵐ p ∂Measure.count[| (permutationHistory positions reference : Set (Equiv.Perm (Fin n)))],
      p ∈ permutationHistory positions reference
    exact ae_cond_mem (by measurability)
  have hb : ∀ᵐ p ∂μ, X p ∈ Set.Icc (c * lo) (c * upper) := by
    filter_upwards [hmem] with p hp
    have hu := permutationHistory_next_unused positions reference p i hi hp
    obtain ⟨hl, hr⟩ := hbound (p i) hu
    exact ⟨mul_le_mul_of_nonneg_left hl hc, mul_le_mul_of_nonneg_left hr hc⟩
  exact hasSubgaussianMGF_of_mem_Icc hm hb

/-- Integration against a history measure is the exact average over its
finite fiber. -/
theorem permutationHistory_integral {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (f : Equiv.Perm (Fin n) → ℝ) :
    (permutationHistoryMeasure positions reference)[f] =
      (∑ p ∈ permutationHistory positions reference, f p) /
        (permutationHistory positions reference).card := by
  classical
  have hint : Integrable f (Measure.count : Measure (Equiv.Perm (Fin n))) := by
    apply integrable_count_iff.mpr
    exact Summable.of_finite
  have his : IntegrableOn f (permutationHistory positions reference : Set (Equiv.Perm (Fin n)))
      (Measure.count : Measure (Equiv.Perm (Fin n))) := hint.integrableOn
  unfold permutationHistoryMeasure uniformOn ProbabilityTheory.cond
  rw [integral_smul_measure, setIntegral_finset _ his]
  simp [measureReal_def, div_eq_mul_inv, mul_comm]

/-- The conditional mean of the next revealed value is the average over
exactly the unused values. -/
theorem permutationHistory_next_mean {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (values : Fin n → ℝ) :
    (permutationHistoryMeasure positions reference)[fun p => values (p i)] =
      (∑ b ∈ (positions.image reference)ᶜ, values b) / (n - positions.card : ℕ) := by
  have hh : 0 < (permutationHistory positions reference).card := by
    apply Finset.card_pos.mpr
    exact ⟨reference, by simp [permutationHistory]⟩
  have hH : ((permutationHistory positions reference).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hh)
  have hlt : positions.card < n := by
    simpa using Finset.card_lt_univ_of_notMem hi
  have hK : ((n - positions.card : ℕ) : ℝ) ≠ 0 := by
    have hn : n - positions.card ≠ 0 := by omega
    exact_mod_cast hn
  rw [permutationHistory_integral]
  apply (div_eq_div_iff hH hK).2
  have h := permutationHistory_next_sum positions reference i hi values
  nlinarith [h]

/-- Hoeffding's bound centered at the actual unused-value average, rather
than at an abstract integral. -/
theorem permutationHistory_next_explicit_subgaussian {n : ℕ} (positions : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (values : Fin n → ℝ) (c lo upper : ℝ) (hc : 0 ≤ c)
    (hbound : ∀ a, a ∉ positions.image reference → values a ∈ Set.Icc lo upper) :
    let μ := permutationHistoryMeasure positions reference
    let m := (∑ b ∈ (positions.image reference)ᶜ, values b) / (n - positions.card : ℕ)
    HasSubgaussianMGF (fun p => c * (values (p i) - m))
      ((‖c * upper - c * lo‖₊ / 2) ^ 2) μ := by
  have h := permutationHistory_next_subgaussian positions reference i hi values c lo upper hc hbound
  dsimp only at h ⊢
  rw [integral_const_mul, permutationHistory_next_mean positions reference i hi values] at h
  convert h using 1
  funext p
  ring

/-- The conditional expected contribution of all unrevealed weighted slots
is their total weight times the common unused-value mean. -/
theorem permutationHistory_weighted_mean {n : ℕ} (positions remaining : Finset (Fin n))
    (reference : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (hdis : Disjoint remaining positions) (weights values : Fin n → ℝ) :
    (permutationHistoryMeasure positions reference)[fun p => ∑ j ∈ remaining, weights j * values (p j)] =
      (∑ j ∈ remaining, weights j) *
        ((∑ b ∈ (positions.image reference)ᶜ, values b) / (n - positions.card : ℕ)) := by
  have hh : 0 < (permutationHistory positions reference).card := by
    apply Finset.card_pos.mpr
    exact ⟨reference, by simp [permutationHistory]⟩
  have hH : ((permutationHistory positions reference).card : ℝ) ≠ 0 := by
    exact_mod_cast (Nat.ne_of_gt hh)
  have hlt : positions.card < n := by
    simpa using Finset.card_lt_univ_of_notMem hi
  have hK : ((n - positions.card : ℕ) : ℝ) ≠ 0 := by
    have hn : n - positions.card ≠ 0 := by omega
    exact_mod_cast hn
  rw [permutationHistory_integral]
  have h := permutationHistory_weighted_sum positions remaining reference hdis weights values
  field_simp
  nlinarith [h]

end
end Sude
