import Sude.PermutationExposure

/-! The last slot in the permutation exposure is deterministic. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- If exactly one output is unused, every extension of the history gives
that output to the remaining position. -/
theorem permutationHistory_last_value {n : ℕ} (positions : Finset (Fin n))
    (reference p : Equiv.Perm (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (hK : n - positions.card = 1) (hp : p ∈ permutationHistory positions reference) :
    p i = reference i := by
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  have hcard : available.card ≤ 1 := by
    simp [available, Finset.card_compl, Finset.card_image_of_injective _ reference.injective, hK]
  have hp' : p i ∈ available := by
    simpa [available] using permutationHistory_next_unused positions reference p i hi hp
  have href : reference i ∈ available := by
    have h := permutationHistory_next_unused positions reference reference i hi
      (by simp [permutationHistory])
    simpa [available] using h
  exact (Finset.card_le_one_iff.mp hcard) hp' href

/-- With one position left, every disjoint set of slots containing it is
exactly that singleton. -/
theorem permutationHistory_last_remaining {n : ℕ} (positions remaining : Finset (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : n - positions.card = 1)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining) : remaining = {i} := by
  have hcard : positionsᶜ.card ≤ 1 := by simp [Finset.card_compl, hK]
  have hi' : i ∈ positionsᶜ := by simpa using hi
  have hsub : remaining ⊆ positionsᶜ := by
    intro j hj
    simpa using (Finset.disjoint_left.mp hdis) hj
  ext j
  simp only [Finset.mem_singleton]
  constructor
  · intro hj
    exact (Finset.card_le_one_iff.mp hcard) (hsub hj) hi'
  · intro hj
    subst j
    exact hslot

/-- The last reveal changes no conditional prediction, almost surely. -/
theorem permutationHistory_last_increment_ae {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : n - positions.card = 1)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ) :
    let μ := permutationHistoryMeasure positions reference
    ∀ᵐ p ∂μ, weights i * values (p i) +
      (permutationHistoryMeasure (insert i positions) p)[fun q =>
        ∑ j ∈ remaining.erase i, weights j * values (q j)] -
      μ[fun q => ∑ j ∈ remaining, weights j * values (q j)] = 0 := by
  let μ := permutationHistoryMeasure positions reference
  have hrem := permutationHistory_last_remaining positions remaining i hi hK hdis hslot
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  have havcard : available.card ≤ 1 := by
    simp [available, Finset.card_compl, Finset.card_image_of_injective _ reference.injective, hK]
  have href : reference i ∈ available := by
    have h := permutationHistory_next_unused positions reference reference i hi
      (by simp [permutationHistory])
    simpa [available] using h
  have hav : available = {reference i} := by
    ext b
    simp only [Finset.mem_singleton]
    constructor
    · intro hb
      exact (Finset.card_le_one_iff.mp havcard) hb href
    · intro hb
      subst b
      exact href
  have hmean : μ[fun q => ∑ j ∈ remaining, weights j * values (q j)] =
      weights i * values (reference i) := by
    rw [hrem]
    simp only [Finset.sum_singleton]
    rw [integral_const_mul, permutationHistory_next_mean positions reference i hi values]
    change weights i * ((∑ b ∈ available, values b) / (n - positions.card : ℕ)) = _
    simp [hav, hK]
  have hmem : ∀ᵐ p ∂μ, p ∈ permutationHistory positions reference := by
    change ∀ᵐ p ∂Measure.count[| (permutationHistory positions reference : Set (Equiv.Perm (Fin n)))],
      p ∈ permutationHistory positions reference
    exact ae_cond_mem (by measurability)
  filter_upwards [hmem] with p hp
  have hpi := permutationHistory_last_value positions reference p i hi hK hp
  rw [hmean, hpi]
  simp [hrem]

/-- A deterministic final increment is sub-Gaussian with variance proxy zero. -/
theorem permutationHistory_last_subgaussian {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : n - positions.card = 1)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ) :
    let μ := permutationHistoryMeasure positions reference
    HasSubgaussianMGF (fun p => weights i * values (p i) +
      (permutationHistoryMeasure (insert i positions) p)[fun q =>
        ∑ j ∈ remaining.erase i, weights j * values (q j)] -
      μ[fun q => ∑ j ∈ remaining, weights j * values (q j)]) 0 μ := by
  let μ := permutationHistoryMeasure positions reference
  have : IsProbabilityMeasure μ := permutationHistoryMeasure_isProbability positions reference
  have hz : HasSubgaussianMGF (fun _ : Equiv.Perm (Fin n) => 0) 0 μ := HasSubgaussianMGF.fun_zero
  apply hz.congr
  filter_upwards [permutationHistory_last_increment_ae positions remaining reference i hi hK hdis hslot weights values] with p hp
  exact hp.symm

end
end Sude
