import Sude.PrefixSortedLabelSplit
import Sude.PrefixDepthMeanIdentity

/-! A supplied balanced ordered split has valid child and parent means,
including empty and singleton populations. No slot allocation is asserted. -/
namespace Sude
noncomputable section

/-- A specified ordered lower half admits suitable child means. Nonempty
children use their actual numerical means; an empty child's mean is chosen
harmlessly. The parent mean is the weighted average with exact child sizes. -/
theorem prefix_local_balanced_mean_split {α : Type*} [DecidableEq α]
    (A T : Finset α) (x : α → ℝ) (C : ℝ) (hC : 0 ≤ C)
    (hTA : T ⊆ A) (hcard : T.card = A.card / 2)
    (horder : ∀ a ∈ T, ∀ b ∈ A \ T, x a ≤ x b)
    (hwidth : ∀ a ∈ A, ∀ b ∈ A, x b - x a ≤ C) :
    ∃ (low high : ℝ),
      (T.Nonempty → low = (∑ a ∈ T, x a) / T.card) ∧
      ((A \ T).Nonempty → high = (∑ a ∈ A \ T, x a) / (A \ T).card) ∧
      0 ≤ high - low ∧ high - low ≤ C ∧
      (∑ a ∈ A, x a) / A.card =
        ((A.card / 2 : ℕ) : ℝ) / A.card * low +
          (1 - ((A.card / 2 : ℕ) : ℝ) / A.card) * high := by
  classical
  by_cases hlarge : 2 ≤ A.card
  · have hrest : (A \ T).card = A.card - A.card / 2 := by
      rw [Finset.card_sdiff_of_subset hTA, hcard]
    have hTpos : 0 < T.card := by rw [hcard]; omega
    have hRpos : 0 < (A \ T).card := by rw [hrest]; omega
    have hT := Finset.card_pos.mp hTpos
    have hR := Finset.card_pos.mp hRpos
    have hg := prefix_finite_split_mean_gap T (A \ T) x x C hT hR (by
      intro a ha b hb
      exact ⟨sub_nonneg.mpr (horder a ha b hb),
        hwidth a (hTA ha) b (Finset.mem_sdiff.mp hb).1⟩)
    let low : ℝ := (∑ a ∈ T, x a) / T.card
    let high : ℝ := (∑ a ∈ A \ T, x a) / (A \ T).card
    refine ⟨low, high, (fun _ => rfl), (fun _ => rfl), hg.1, hg.2, ?_⟩
    have hq : 0 < A.card := by omega
    have hm : A.card / 2 ≤ A.card := Nat.div_le_self _ _
    have hq0 : (A.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hq)
    have ht0 : (T.card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hTpos)
    have hr0 : ((A \ T).card : ℝ) ≠ 0 := by exact_mod_cast (Nat.ne_of_gt hRpos)
    have hsum : (∑ a ∈ T, x a) + (∑ a ∈ A \ T, x a) = ∑ a ∈ A, x a := by
      simpa [add_comm] using Finset.sum_sdiff (f := x) hTA
    have htot : (A.card : ℝ) * ((∑ a ∈ A, x a) / A.card) =
        ((A.card / 2 : ℕ) : ℝ) * low + ((A.card - A.card / 2 : ℕ) : ℝ) * high := by
      rw [← hrest, ← hcard]
      dsimp [low, high]
      rw [mul_div_cancel₀ _ hq0, mul_div_cancel₀ _ ht0, mul_div_cancel₀ _ hr0]
      linarith
    exact prefix_parent_mean_from_child_totals A.card (A.card / 2)
      ((∑ a ∈ A, x a) / A.card) low high hq hm htot
  · have hdiv : A.card / 2 = 0 := by omega
    have hT : T = ∅ := Finset.card_eq_zero.mp (by omega)
    let μ : ℝ := (∑ a ∈ A, x a) / A.card
    refine ⟨μ, μ, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hT]; simp
    · intro _; simp [hT, μ]
    · simp
    · simpa using hC
    · simp [hdiv, μ]

end
end Sude
