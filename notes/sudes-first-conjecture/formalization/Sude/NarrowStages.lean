import Sude.PhysicalNarrowing
import Sude.BTSourceGate

/-! Initial and BT stages with the source's paid candidate narrowing. -/
namespace Sude
noncomputable section

/-- Narrow any already selected `zQ`-pair stage and retain only `Q` pairs.
The discarded candidates are not removed from the actual unused stock. -/
theorem narrow_selected_stage (unused candidates : Finset ℕ) (h z Q : ℕ)
    (lo width : ℝ) (hh : 0 < h) (hcard : candidates.card = z * Q)
    (hmatch : PairwiseDisjointPairs candidates h) (hfoot : pairFootprint candidates h ⊆ unused)
    (hz : 0 < z) (hwidth : 0 < width)
    (hspan : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) < lo + z * width) :
    ∃ chosen : Finset ℕ, chosen.card = Q ∧ PairwiseDisjointPairs chosen h ∧
      pairFootprint chosen h ⊆ unused ∧ (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + h : ℕ)) / 2) - (((q : ℝ) + (q + h : ℕ)) / 2)| < width) := by
  have havail : ∀ p ∈ candidates, p ∈ unused ∧ p + h ∈ unused := by
    intro p hp
    exact ⟨hfoot (Finset.mem_union_left _ hp),
      hfoot (Finset.mem_union_right _ (Finset.mem_image.mpr ⟨p, hp, rfl⟩))⟩
  have hspan' : ∀ p ∈ candidates, lo ≤ p ∧ (p : ℝ) < lo + z * width := by
    intro p hp
    exact hspan p (havail p hp).1
  obtain ⟨chosen, _, hc, hm, hs, hf, hremain, hn⟩ :=
    narrow_matching_and_deplete unused candidates lo width z Q h hz hwidth hh hspan'
      (by rw [hcard]) havail hmatch
  exact ⟨chosen, hc, hm, hs, hf, hremain, hn⟩

/-- One elementary AP stage, with the source's `zQ` candidate budget and
the midpoint-narrowed retained `Q`-batch. -/
theorem ap_narrow_interval_stage (unused classes : Finset ℕ)
    (lo c X r R L η M gapWidth midLo midWidth : ℝ) (g z Q : ℕ)
    (hne : unused.Nonempty)
    (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ unused, p % g ∈ classes)
    (hM : 0 ≤ M) (hNM : M ≤ unused.card) (hc : 0 ≤ c) (hX : 0 < X)
    (hr : 0 < r) (hR : 0 < R) (hL : 0 < L) (hg : 0 < g)
    (hclasscount : (classes.card : ℝ) ≤ r)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hradius : R ≤ X / L) (hgapWidth : 0 < gapWidth)
    (hgapEq : gapWidth = g * (η * M * R / (r * X) - 1 / 2))
    (hbudget : 2 * ((z * Q : ℕ) : ℝ) * r * X ≤
      (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g)
    (hz : 0 < z) (hmidWidth : 0 < midWidth)
    (hspan : ∀ p ∈ unused, midLo ≤ p ∧ (p : ℝ) < midLo + z * midWidth) :
    ∃ (h : ℕ) (chosen : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ ⌊R⌋₊ ∧ gapWidth ≤ h ∧
      chosen.card = Q ∧ PairwiseDisjointPairs chosen h ∧ pairFootprint chosen h ⊆ unused ∧
      (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + h : ℕ)) / 2) - (((q : ℝ) + (q + h : ℕ)) / 2)| < midWidth) := by
  obtain ⟨h, candidates, hh, hdiv, hR', hmin, hcard, hmatch, hfoot, _, _⟩ :=
    ap_interval_stage_from_source_budget unused classes lo c X r R L η M gapWidth g (z * Q)
      hne hinterval hclasses hM hNM hc hX hr hR hL hg hclasscount hη hε hradius hgapWidth hgapEq hbudget
  obtain ⟨chosen, hc', hm, hs, hf, hremain, hn⟩ :=
    narrow_selected_stage unused candidates h z Q midLo midWidth hh hcard hmatch hfoot hz hmidWidth hspan
  exact ⟨h, chosen, hh, hdiv, hR', hmin, hc', hm, hs, hf, hremain, hn⟩

/-- One BT stage with `zQ` candidate pairs and only `Q` actual retained
pairs, with the exact midpoint and depletion invariants. -/
theorem mv_narrow_interval_stage (mv : MVBrunTitchmarsh) (unused classes : Finset ℕ)
    (lo c X r R L η M ell gapWidth midLo midWidth : ℝ) (g z Q : ℕ)
    (hne : unused.Nonempty) (hprimes : ∀ p ∈ unused, Nat.Prime p)
    (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ unused, p % g ∈ classes)
    (hreduced : ∀ a ∈ classes, 0 < a ∧ Nat.Coprime g a)
    (hM : 0 ≤ M) (hNM : M ≤ unused.card) (hc : 0 ≤ c) (hX : 0 < X)
    (hr : 0 < r) (hR : 0 < R) (hL : 0 < L) (hg : 0 < g) (hell : 0 < ell)
    (hclasscount : (classes.card : ℝ) ≤ r)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hradius : R ≤ X / L)
    (hgapEq : gapWidth = (ell * (Nat.totient g : ℝ) / (2 * g)) * g *
      (η * M * R / (r * X) - 1 / 2))
    (hentry : Real.exp ell ≤ gapWidth / g)
    (hbudget : 2 * ((z * Q : ℕ) : ℝ) * r * X ≤
      (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g)
    (hz : 0 < z) (hmidWidth : 0 < midWidth)
    (hspan : ∀ p ∈ unused, midLo ≤ p ∧ (p : ℝ) < midLo + z * midWidth) :
    ∃ (h : ℕ) (chosen : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ ⌊R⌋₊ ∧ gapWidth ≤ h ∧
      chosen.card = Q ∧ PairwiseDisjointPairs chosen h ∧ pairFootprint chosen h ⊆ unused ∧
      (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card ∧
      (∀ p ∈ chosen, ∀ q ∈ chosen,
        |(((p : ℝ) + (p + h : ℕ)) / 2) - (((q : ℝ) + (q + h : ℕ)) / 2)| < midWidth) := by
  obtain ⟨h, candidates, hh, hdiv, hR', hmin, hcard, hmatch, hfoot, _, _⟩ :=
    mv_interval_stage_from_source_budget mv unused classes lo c X r R L η M ell gapWidth g (z * Q)
      hne hprimes hinterval hclasses hreduced hM hNM hc hX hr hR hL hg hell hclasscount hη hε
      hradius hgapEq hentry hbudget
  obtain ⟨chosen, hc', hm, hs, hf, hremain, hn⟩ :=
    narrow_selected_stage unused candidates h z Q midLo midWidth hh hcard hmatch hfoot hz hmidWidth hspan
  exact ⟨h, chosen, hh, hdiv, hR', hmin, hc', hm, hs, hf, hremain, hn⟩

end
end Sude
