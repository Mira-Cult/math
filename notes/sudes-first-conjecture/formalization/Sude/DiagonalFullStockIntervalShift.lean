import Sude.DiagonalFullStockDeletion

/-! Charge the shifted post-diagonal interval against a widened old interval. -/
namespace Sude
noncomputable section

/-- An explicit center displacement embeds one half-open prime interval in
the old-centered interval widened on both sides by that displacement. -/
theorem ap_interval_shift_subset (μ₀ μ₁ radius δ : ℝ)
    (hradius : 0 ≤ radius) (hshift : |μ₁ - μ₀| ≤ δ)
    (hleft : 0 ≤ μ₀ - radius - δ) :
    apInterval (μ₁ - radius) (μ₁ + radius) 2 1 ⊆
      apInterval (μ₀ - radius - δ) (μ₀ + radius + δ) 2 1 := by
  intro p hp
  have hδ : 0 ≤ δ := le_trans (abs_nonneg _) hshift
  have hs := abs_le.mp hshift
  have hpostlo : 0 ≤ μ₁ - radius := by linarith [hs.1]
  have hposthi : 0 ≤ μ₁ + radius := by linarith
  have holdhi : 0 ≤ μ₀ + radius + δ := by linarith
  have hp' := (mem_apInterval_iff _ _ 2 1 hpostlo hposthi p).mp hp
  apply (mem_apInterval_iff _ _ 2 1 hleft holdhi p).mpr
  exact ⟨hp'.1, by linarith [hp'.2.1, hs.1], by linarith [hp'.2.2.1, hs.2], hp'.2.2.2⟩

/-- The original reserved entries are charged in the widened old-centered
interval, and the new diagonal entries add at most 2n−1. The old count,
endpoint margin and numerical supply gate remain separate hypotheses. -/
theorem post_diagonal_deletions_from_widened_interval {n : ℕ}
    (a b : Cell n ≃ Fin (n * n)) (reserved : Finset (Cell n))
    (μ₀ μ₁ radius δ : ℝ) (hn : 0 < n) (hodd : Odd n)
    (hfixed : ∀ z ∈ reserved, entry b z = entry a z)
    (hradius : 0 ≤ radius) (hshift : |μ₁ - μ₀| ≤ δ)
    (hleft : 0 ≤ μ₀ - radius - δ) :
    (apInterval (μ₁ - radius) (μ₁ + radius) 2 1 ∩
      (reserved ∪ unreservedDiagonalCells reserved).image (entry b)).card ≤
    (apInterval (μ₀ - radius - δ) (μ₀ + radius + δ) 2 1 ∩
      reserved.image (entry a)).card + (2 * n - 1) := by
  have hsub : apInterval (μ₁ - radius) (μ₁ + radius) 2 1 ∩ reserved.image (entry a) ⊆
      apInterval (μ₀ - radius - δ) (μ₀ + radius + δ) 2 1 ∩ reserved.image (entry a) := by
    intro p hp
    exact Finset.mem_inter.mpr ⟨ap_interval_shift_subset μ₀ μ₁ radius δ hradius hshift hleft
      (Finset.mem_inter.mp hp).1, (Finset.mem_inter.mp hp).2⟩
  have hc := Finset.card_le_card hsub
  have hd := post_diagonal_interval_deletion_two_n a b reserved (μ₁ - radius) (μ₁ + radius)
    hn hodd hfixed
  omega

end
end Sude
