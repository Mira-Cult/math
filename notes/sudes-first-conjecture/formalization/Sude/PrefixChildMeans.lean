import Sude.CentralWindow

/-! Arithmetic link between labelled value-set means and the parent/child
mean hypothesis used in one simultaneous prefix-rounding depth. -/
namespace Sude
noncomputable section

/-- The total of a finite labelled population is its cardinality times its
mean, even for the empty population, using Lean's totalized real division. -/
theorem prefix_card_mul_mean {A : Type*} (B : Finset A) (v : A → ℝ) :
    (B.card : ℝ) * ((∑ a ∈ B, v a) / B.card) = ∑ a ∈ B, v a := by
  classical
  by_cases hzero : B.card = 0
  · have hB : B = ∅ := Finset.card_eq_zero.mp hzero
    simp [hB]
  · have hreal : (B.card : ℝ) ≠ 0 := by exact_mod_cast hzero
    field_simp

/-- The mean of a nonempty parent labelled set is the cardinality-weighted
mean of a subset and its complement. The child sets may be empty. -/
theorem prefix_parent_mean_from_child_sets {A : Type*} [DecidableEq A] (B T : Finset A) (v : A → ℝ)
    (hTB : T ⊆ B) (hB : B.Nonempty) :
    (∑ a ∈ B, v a) / B.card =
      ((T.card : ℝ) / B.card) * ((∑ a ∈ T, v a) / T.card) +
      (1 - (T.card : ℝ) / B.card) *
        ((∑ a ∈ B \ T, v a) / (B \ T).card) := by
  classical
  have hq0 : (B.card : ℝ) ≠ 0 := by
    exact_mod_cast (Finset.card_ne_zero.mpr hB)
  have hcard : ((B \ T).card : ℝ) = (B.card : ℝ) - T.card := by
    have h := Finset.card_sdiff_add_card_eq_card hTB
    have hc : ((B \ T).card : ℝ) + T.card = B.card := by exact_mod_cast h
    linarith
  have hs : (∑ a ∈ B, v a) = (∑ a ∈ T, v a) + ∑ a ∈ B \ T, v a := by
    simpa [add_comm] using (Finset.sum_sdiff (f := v) hTB).symm
  have ht := prefix_card_mul_mean T v
  have hc := prefix_card_mul_mean (B \ T) v
  let lo : ℝ := (∑ a ∈ T, v a) / T.card
  let hi : ℝ := (∑ a ∈ B \ T, v a) / (B \ T).card
  change (T.card : ℝ) * lo = ∑ a ∈ T, v a at ht
  change ((B \ T).card : ℝ) * hi = ∑ a ∈ B \ T, v a at hc
  change (∑ a ∈ B, v a) / B.card =
    ((T.card : ℝ) / B.card) * lo + (1 - (T.card : ℝ) / B.card) * hi
  apply (div_eq_iff hq0).mpr
  rw [hs, ← ht, ← hc, hcard]
  field_simp


end
end Sude
