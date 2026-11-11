import Sude.PermutationHoeffding

/-! Finite-set bookkeeping for the permutation exposure martingale. -/
namespace Sude
noncomputable section
open MeasureTheory ProbabilityTheory
open scoped ProbabilityTheory
local instance (n : ℕ) : MeasurableSpace (Equiv.Perm (Fin n)) := ⊤

/-- Revealing a new position reduces the number of unrevealed positions by
exactly one, without truncated-subtraction ambiguity. -/
theorem permutationHistory_insert_remaining_card {n : ℕ} (positions : Finset (Fin n))
    (i : Fin n) (hi : i ∉ positions) :
    (insert i positions).card = positions.card + 1 ∧
      (n - (insert i positions).card) + 1 = n - positions.card := by
  have hcard : (insert i positions).card = positions.card + 1 := by
    simp [Finset.card_insert_of_notMem hi]
  have hlt : positions.card < n := by
    simpa using Finset.card_lt_univ_of_notMem hi
  constructor
  · exact hcard
  · omega

/-- The sum of unused values after a reveal is the earlier sum less the
observed value. -/
theorem permutationHistory_insert_unused_sum {n : ℕ} (positions : Finset (Fin n))
    (reference p : Equiv.Perm (Fin n)) (i a : Fin n) (hi : i ∉ positions)
    (hp : p ∈ permutationHistoryNext positions reference i a) (values : Fin n → ℝ) :
    (∑ b ∈ ((insert i positions).image p)ᶜ, values b) =
      (∑ b ∈ (positions.image reference)ᶜ, values b) - values a := by
  have hp' : p ∈ permutationHistory positions reference ∧ p i = a := Finset.mem_filter.mp hp
  have ha : a ∉ positions.image reference := by
    rw [← hp'.2]
    exact permutationHistory_next_unused positions reference p i hi hp'.1
  let available : Finset (Fin n) := (positions.image reference)ᶜ
  have hmem : a ∈ available := by simpa [available] using ha
  have hset : ((insert i positions).image p)ᶜ = available.erase a := by
    rw [permutationHistoryNext_image_insert positions reference p i a hp]
    ext b
    simp [available]
  rw [hset]
  have hsum := Finset.sum_erase_add available values hmem
  linarith

/-- After a nonfinal reveal, the conditional mean of the remaining weighted
slots uses exactly the depleted value pool and one fewer position. -/
theorem permutationHistory_after_weighted_mean {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference p : Equiv.Perm (Fin n))
    (i a : Fin n) (hi : i ∉ positions) (hp : p ∈ permutationHistoryNext positions reference i a)
    (hK : 2 ≤ n - positions.card) (hdis : Disjoint remaining positions)
    (weights values : Fin n → ℝ) :
    (permutationHistoryMeasure (insert i positions) p)[fun q => ∑ j ∈ remaining.erase i, weights j * values (q j)] =
      (∑ j ∈ remaining.erase i, weights j) *
        (((∑ b ∈ (positions.image reference)ᶜ, values b) - values a) /
          (n - positions.card - 1 : ℕ)) := by
  classical
  have hc := permutationHistory_insert_remaining_card positions i hi
  have hlt : (insert i positions).card < n := by omega
  have hne : insert i positions ≠ Finset.univ := by
    apply (Finset.card_lt_iff_ne_univ _).mp
    simpa using hlt
  obtain ⟨j, hj⟩ : ∃ j, j ∉ insert i positions := by
    by_contra h
    apply hne
    apply Finset.eq_univ_iff_forall.mpr
    intro j
    by_contra hj
    exact h ⟨j, hj⟩
  have hdis' : Disjoint (remaining.erase i) (insert i positions) := by
    apply Finset.disjoint_left.mpr
    intro j hj hj'
    simp only [Finset.mem_erase] at hj
    simp only [Finset.mem_insert] at hj'
    rcases hj' with rfl | hj'
    · exact hj.1 rfl
    · exact (Finset.disjoint_left.mp hdis) hj.2 hj'
  have h := permutationHistory_weighted_mean (insert i positions) (remaining.erase i) p j hj
    hdis' weights values
  rw [permutationHistory_insert_unused_sum positions reference p i a hi hp values] at h
  have hnat : n - (insert i positions).card = n - positions.card - 1 := by omega
  rw [hnat] at h
  exact h

/-- The actual change in the conditional mean on a nonfinal reveal is the
source's weighted-permutation increment, with no independent-draw hypothesis. -/
theorem permutationHistory_reveal_increment {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference p : Equiv.Perm (Fin n))
    (i a : Fin n) (hi : i ∉ positions) (hp : p ∈ permutationHistoryNext positions reference i a)
    (hK : 2 ≤ n - positions.card) (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ) :
    weights i * values a +
      (permutationHistoryMeasure (insert i positions) p)[fun q =>
        ∑ j ∈ remaining.erase i, weights j * values (q j)] -
      (permutationHistoryMeasure positions reference)[fun q =>
        ∑ j ∈ remaining, weights j * values (q j)] =
      (weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ)) *
        (values a - (∑ b ∈ (positions.image reference)ᶜ, values b) / (n - positions.card : ℕ)) := by
  have hR : (1 : ℝ) < ((n - positions.card : ℕ) : ℝ) := by
    exact_mod_cast (show 1 < n - positions.card by omega)
  have hR0 : ((n - positions.card : ℕ) : ℝ) ≠ 0 := by linarith
  have hR1 : ((n - positions.card : ℕ) : ℝ) - 1 ≠ 0 := by linarith
  have hcast : ((n - positions.card - 1 : ℕ) : ℝ) = ((n - positions.card : ℕ) : ℝ) - 1 := by
    have hnon : 1 ≤ n - positions.card := by omega
    rw [Nat.cast_sub hnon]
    norm_num
  rw [permutationHistory_after_weighted_mean positions remaining reference p i a hi hp hK hdis weights values,
    permutationHistory_weighted_mean positions remaining reference i hi hdis weights values,
    ← Finset.sum_erase_add remaining weights hslot, hcast]
  field_simp
  ring

/-- Hoeffding's bound for the actual weighted-mean increment on a nonfinal
reveal, conditional on the realized history. -/
theorem permutationHistory_reveal_subgaussian {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : 2 ≤ n - positions.card)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ) (lo upper : ℝ)
    (hbound : ∀ a, a ∉ positions.image reference → values a ∈ Set.Icc lo upper)
    (hc : 0 ≤ weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ)) :
    let c := weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ)
    let μ := permutationHistoryMeasure positions reference
    HasSubgaussianMGF (fun p => weights i * values (p i) +
      (permutationHistoryMeasure (insert i positions) p)[fun q =>
        ∑ j ∈ remaining.erase i, weights j * values (q j)] -
      μ[fun q => ∑ j ∈ remaining, weights j * values (q j)])
      ((‖c * upper - c * lo‖₊ / 2) ^ 2) μ := by
  let c := weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ)
  let μ := permutationHistoryMeasure positions reference
  have hsub := permutationHistory_next_explicit_subgaussian positions reference i hi values c lo upper hc hbound
  dsimp only at hsub ⊢
  apply hsub.congr
  have hmem : ∀ᵐ p ∂μ, p ∈ permutationHistory positions reference := by
    change ∀ᵐ p ∂Measure.count[| (permutationHistory positions reference : Set (Equiv.Perm (Fin n)))],
      p ∈ permutationHistory positions reference
    exact ae_cond_mem (by measurability)
  filter_upwards [hmem] with p hp
  have hp' : p ∈ permutationHistoryNext positions reference i (p i) := Finset.mem_filter.mpr ⟨hp, rfl⟩
  exact (permutationHistory_reveal_increment positions remaining reference p i (p i) hi hp'
    hK hdis hslot weights values).symm

/-- Decreasing nonnegative remaining weights imply the exact reveal
coefficient is between zero and the current weight. -/
theorem permutationHistory_reveal_coefficient_bounds {n : ℕ}
    (positions remaining : Finset (Fin n)) (i : Fin n) (hi : i ∉ positions)
    (hK : 2 ≤ n - positions.card) (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights : Fin n → ℝ) (hnonneg : ∀ j ∈ remaining, 0 ≤ weights j)
    (horder : ∀ j ∈ remaining.erase i, weights j ≤ weights i) :
    0 ≤ weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ) ∧
      weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ) ≤ weights i := by
  classical
  have hsub : remaining.erase i ⊆ (insert i positions)ᶜ := by
    intro j hj
    simp only [Finset.mem_erase] at hj
    simp only [Finset.mem_compl, Finset.mem_insert]
    intro h
    rcases h with rfl | h
    · exact hj.1 rfl
    · exact (Finset.disjoint_left.mp hdis) hj.2 h
  have hsize : (remaining.erase i).card ≤ n - positions.card - 1 := by
    have h := Finset.card_le_card hsub
    have hc := permutationHistory_insert_remaining_card positions i hi
    rw [Finset.card_compl, Fintype.card_fin] at h
    omega
  have hsizereal : ((remaining.erase i).card : ℝ) ≤ ((n - positions.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast hsize
  have hwi : 0 ≤ weights i := hnonneg i hslot
  have hsum := weightedRemaining_sum_bounds (remaining.erase i) weights (weights i)
    (fun j hj => hnonneg j (Finset.mem_of_mem_erase hj)) horder
  have hden : 0 < ((n - positions.card - 1 : ℕ) : ℝ) := by
    exact_mod_cast (show 0 < n - positions.card - 1 by omega)
  have hratio0 : 0 ≤ (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ) :=
    div_nonneg hsum.1 (le_of_lt hden)
  have hratio : (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ) ≤ weights i := by
    apply (div_le_iff₀ hden).2
    calc
      _ ≤ ((remaining.erase i).card : ℝ) * weights i := hsum.2
      _ ≤ ((n - positions.card - 1 : ℕ) : ℝ) * weights i := mul_le_mul_of_nonneg_right hsizereal hwi
      _ = _ := mul_comm _ _
  constructor <;> linarith

/-- The increment bound applies under the source's ordering of nonnegative
weights, with coefficient positivity proved from the physical number of
remaining slots. -/
theorem permutationHistory_reveal_ordered_subgaussian {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : 2 ≤ n - positions.card)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ) (lo upper : ℝ)
    (hnonneg : ∀ j ∈ remaining, 0 ≤ weights j)
    (horder : ∀ j ∈ remaining.erase i, weights j ≤ weights i)
    (hbound : ∀ a, a ∉ positions.image reference → values a ∈ Set.Icc lo upper) :
    let c := weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ)
    let μ := permutationHistoryMeasure positions reference
    HasSubgaussianMGF (fun p => weights i * values (p i) +
      (permutationHistoryMeasure (insert i positions) p)[fun q =>
        ∑ j ∈ remaining.erase i, weights j * values (q j)] -
      μ[fun q => ∑ j ∈ remaining, weights j * values (q j)])
      ((‖c * upper - c * lo‖₊ / 2) ^ 2) μ := by
  exact permutationHistory_reveal_subgaussian positions remaining reference i hi hK hdis hslot
    weights values lo upper hbound
    (permutationHistory_reveal_coefficient_bounds positions remaining i hi hK hdis hslot
      weights hnonneg horder).1

/-- Enlarging the variance proxy preserves a proved sub-Gaussian bound. -/
theorem subgaussian_parameter_mono {Ω : Type*} [MeasurableSpace Ω]
    {X : Ω → ℝ} {μ : Measure Ω} {c d : NNReal}
    (h : HasSubgaussianMGF X c μ) (hcd : c ≤ d) : HasSubgaussianMGF X d μ := by
  refine ⟨h.integrable_exp_mul, ?_⟩
  intro t
  calc
    mgf X μ t ≤ Real.exp ((c : ℝ) * t ^ 2 / 2) := h.mgf_le t
    _ ≤ Real.exp ((d : ℝ) * t ^ 2 / 2) := by
      apply Real.exp_le_exp.mpr
      have h' : (c : ℝ) ≤ d := NNReal.coe_le_coe.mpr hcd
      have hm := mul_le_mul_of_nonneg_right h' (sq_nonneg t)
      linarith

/-- Source-form one-step bound: the actual coefficient is bounded by the
current weight, so its Hoeffding proxy may use the current weight and the
full remaining value range. -/
theorem permutationHistory_reveal_source_subgaussian {n : ℕ}
    (positions remaining : Finset (Fin n)) (reference : Equiv.Perm (Fin n))
    (i : Fin n) (hi : i ∉ positions) (hK : 2 ≤ n - positions.card)
    (hdis : Disjoint remaining positions) (hslot : i ∈ remaining)
    (weights values : Fin n → ℝ) (lo upper : ℝ)
    (hnonneg : ∀ j ∈ remaining, 0 ≤ weights j)
    (horder : ∀ j ∈ remaining.erase i, weights j ≤ weights i)
    (hbound : ∀ a, a ∉ positions.image reference → values a ∈ Set.Icc lo upper) :
    let μ := permutationHistoryMeasure positions reference
    HasSubgaussianMGF (fun p => weights i * values (p i) +
      (permutationHistoryMeasure (insert i positions) p)[fun q =>
        ∑ j ∈ remaining.erase i, weights j * values (q j)] -
      μ[fun q => ∑ j ∈ remaining, weights j * values (q j)])
      ((‖weights i * upper - weights i * lo‖₊ / 2) ^ 2) μ := by
  let c := weights i - (∑ j ∈ remaining.erase i, weights j) / (n - positions.card - 1 : ℕ)
  have hc := permutationHistory_reveal_coefficient_bounds positions remaining i hi hK hdis hslot
    weights hnonneg horder
  have href : reference ∈ permutationHistory positions reference := by simp [permutationHistory]
  have hunused := permutationHistory_next_unused positions reference reference i hi href
  have hbounds := hbound (reference i) hunused
  have hwidth : 0 ≤ upper - lo := by linarith [hbounds.1, hbounds.2]
  have hw : 0 ≤ weights i := hnonneg i hslot
  have hnormR : ‖c * upper - c * lo‖ ≤ ‖weights i * upper - weights i * lo‖ := by
    rw [show c * upper - c * lo = c * (upper - lo) by ring,
      show weights i * upper - weights i * lo = weights i * (upper - lo) by ring]
    rw [Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (mul_nonneg hc.1 hwidth), abs_of_nonneg (mul_nonneg hw hwidth)]
    exact mul_le_mul_of_nonneg_right hc.2 hwidth
  have hnorm : ‖c * upper - c * lo‖₊ ≤ ‖weights i * upper - weights i * lo‖₊ := by
    apply NNReal.coe_le_coe.mp
    simpa using hnormR
  have hparam : (‖c * upper - c * lo‖₊ / 2) ^ 2 ≤
      (‖weights i * upper - weights i * lo‖₊ / 2) ^ 2 := by
    gcongr
  apply subgaussian_parameter_mono
    (permutationHistory_reveal_ordered_subgaussian positions remaining reference i hi hK hdis hslot
      weights values lo upper hnonneg horder hbound)
  exact hparam

end
end Sude
