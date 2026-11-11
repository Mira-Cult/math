import Sude.APShortPairs
import Sude.BTSourceGate

/-! Initial elementary phase under the source continuous pair budget. -/
namespace Sude
noncomputable section

/-- The same BT5 scalar budget pays the exact bin gate for the ordinary AP
phase, whose elementary short-pair charge is `width/g`. -/
theorem ap_source_implies_exact_bin_gate
    (unused classes : Finset ℕ) (c X r R L η M width : ℝ) (g Q : ℕ)
    (hM : 0 ≤ M) (hNM : M ≤ unused.card) (hc : 0 ≤ c) (hX : 0 < X)
    (hr : 0 < r) (hR : 0 < R) (hL : 0 < L) (hg : 0 < g)
    (hclassespos : 0 < classes.card) (hclasses : (classes.card : ℝ) ≤ r)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hradius : R ≤ X / L)
    (hwidth : width = g * (η * M * R / (r * X) - 1 / 2))
    (hBT5 : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g) :
    (((⌊R⌋₊ / g) * (2 * Q) : ℕ) : ℝ) + (unused.card : ℝ) * (width / g) ≤
      ((unused.card : ℝ) ^ 2 / ((⌊(c * X) / R⌋₊ + 1) * classes.card : ℕ) - unused.card) / 2 := by
  let ell : ℝ := 2 * g / (Nat.totient g : ℝ)
  have hgR : (0 : ℝ) < g := by exact_mod_cast hg
  have hphi : (0 : ℝ) < Nat.totient g := by exact_mod_cast Nat.totient_pos.mpr hg
  have hell : 0 < ell := by dsimp [ell]; positivity
  have hwidth' : width = (ell * (Nat.totient g : ℝ) / (2 * g)) * g *
      (η * M * R / (r * X) - 1 / 2) := by
    rw [hwidth]
    dsimp [ell]
    field_simp
  have hgate := bt_source_implies_exact_bin_gate unused classes c X r R L η M ell width g Q
    hM hNM hc hX hr hR hL hg hell hclassespos hclasses hη hε hradius hwidth' hBT5
  have hratio : 2 * width / ((Nat.totient g : ℝ) * ell) = width / g := by
    dsimp [ell]
    field_simp
  rwa [hratio] at hgate

/-- Select and delete one ordinary initial-phase batch under BT5. The strict
positive-width condition and all numerical inputs are explicit. -/
theorem ap_interval_stage_from_source_budget
    (unused classes : Finset ℕ) (lo c X r R L η M width : ℝ) (g Q : ℕ)
    (hne : unused.Nonempty)
    (hinterval : ∀ p ∈ unused, lo ≤ p ∧ (p : ℝ) ≤ lo + c * X)
    (hclasses : ∀ p ∈ unused, p % g ∈ classes)
    (hM : 0 ≤ M) (hNM : M ≤ unused.card) (hc : 0 ≤ c) (hX : 0 < X)
    (hr : 0 < r) (hR : 0 < R) (hL : 0 < L) (hg : 0 < g)
    (hclasscount : (classes.card : ℝ) ≤ r)
    (hη : 0 ≤ η) (hε : 0 ≤ 1 / (2 * (c + 1 / L)) - η)
    (hradius : R ≤ X / L) (hwidthpos : 0 < width)
    (hwidth : width = g * (η * M * R / (r * X) - 1 / 2))
    (hBT5 : 2 * (Q : ℝ) * r * X ≤ (1 / (2 * (c + 1 / L)) - η) * M ^ 2 * g) :
    ∃ (h : ℕ) (chosen : Finset ℕ), 0 < h ∧ g ∣ h ∧ h ≤ ⌊R⌋₊ ∧ width ≤ h ∧
      chosen.card = Q ∧ PairwiseDisjointPairs chosen h ∧ pairFootprint chosen h ⊆ unused ∧
      (pairFootprint chosen h).card = 2 * Q ∧
      (unused \ pairFootprint chosen h).card + 2 * Q = unused.card := by
  obtain ⟨p, hp⟩ := hne
  have hclasspos : 0 < classes.card := Finset.card_pos.mpr ⟨p % g, hclasses p hp⟩
  have hgate := ap_source_implies_exact_bin_gate unused classes c X r R L η M width g Q
    hM hNM hc hX hr hR hL hg hclasspos hclasscount hη hε hradius hwidth hBT5
  obtain ⟨h, T, hh, hdiv, hRbound, hDbound, hQ, hT, hmatch⟩ :=
    ap_common_gap_from_interval_classes unused classes lo (c * X) R width g Q
      ⟨p, hp⟩ hinterval hclasses hg hR hwidthpos hgate
  obtain ⟨chosen, _, hcard, hm, hs, hf, hremaining⟩ :=
    fixed_gap_select_and_deplete unused T h Q hh hQ hT hmatch
  exact ⟨h, chosen, hh, hdiv, hRbound, hDbound, hcard, hm, hs, hf, hremaining⟩

end
end Sude
