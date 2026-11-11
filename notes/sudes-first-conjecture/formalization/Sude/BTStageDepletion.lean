import Sude.BTIntervalBins

/-! Exact allocation and deletion of a selected common-gap matching. -/
namespace Sude
noncomputable section

/-- Retain exactly `Q` matched pairs from an actual matching and delete their
physical endpoints, with an exact population change. -/
theorem fixed_gap_select_and_deplete (unused candidates : Finset ℕ) (h Q : ℕ)
    (hh : 0 < h) (hQ : Q ≤ candidates.card)
    (havailable : ∀ p ∈ candidates, p ∈ unused ∧ p + h ∈ unused)
    (hmatch : PairwiseDisjointPairs candidates h) :
    ∃ chosen : Finset ℕ, chosen ⊆ candidates ∧ chosen.card = Q ∧
      PairwiseDisjointPairs chosen h ∧ pairFootprint chosen h ⊆ unused ∧
      (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card := by
  obtain ⟨chosen, hsub, hcard⟩ := Finset.exists_subset_card_eq hQ
  have hm : PairwiseDisjointPairs chosen h := by
    intro p hp q hq hpq
    exact hmatch p (hsub hp) q (hsub hq) hpq
  have hs : pairFootprint chosen h ⊆ unused := by
    intro z hz
    rcases Finset.mem_union.mp hz with hz | hz
    · exact (havailable z (hsub hz)).1
    · obtain ⟨p, hp, rfl⟩ := Finset.mem_image.mp hz
      exact (havailable p (hsub hp)).2
  have hf : (pairFootprint chosen h).card = 2 * Q := by
    rw [pairFootprint_card chosen h hh hm, hcard]
  have hremaining := Finset.card_sdiff_add_card_eq_card hs
  rw [hf] at hremaining
  exact ⟨chosen, hsub, hcard, hm, hs, hf, hremaining⟩

/-- A successful bounded BT interval stage supplies exactly `Q` distinct
pairs and leaves exactly the previous unused population less `2Q`. -/
theorem mv_interval_stage_select_and_deplete (mv : MVBrunTitchmarsh)
    (unused classes : Finset ℕ) (lo W radius width ell : ℝ) (g Q : ℕ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + W)
    (hclasses : ∀ p ∈ unused, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hg : 0 < g) (hR : 0 < radius) (hwidth : (g : ℝ) < width)
    (hell : 0 < ell) (hexp : Real.exp ell ≤ width / g)
    (hgate : (((⌊radius⌋₊ / g) * (2 * Q) : ℕ) : ℝ) +
      (unused.card : ℝ) * (2 * width / ((Nat.totient g : ℝ) * ell)) ≤
        ((unused.card : ℝ) ^ 2 / ((⌊W / radius⌋₊ + 1) * classes.card : ℕ) - unused.card) / 2) :
    ∃ (h : ℕ) (chosen : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ ⌊radius⌋₊ ∧ width ≤ h ∧
      chosen.card = Q ∧ PairwiseDisjointPairs chosen h ∧ pairFootprint chosen h ⊆ unused ∧
      (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card := by
  obtain ⟨h, T, hh, hdiv, hRbound, hDbound, hQ, hT, hmatch⟩ :=
    mv_common_gap_from_interval_classes mv unused classes lo W radius width ell g Q
      hne hprimes hinterval hclasses hreduced hg hR hwidth hell hexp hgate
  obtain ⟨chosen, _, hcard, hm, hs, hf, hremaining⟩ :=
    fixed_gap_select_and_deplete unused T h Q hh hQ hT hmatch
  exact ⟨h, chosen, hh, hdiv, hRbound, hDbound, hcard, hm, hs, hf, hremaining⟩

end
end Sude
