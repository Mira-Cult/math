import Sude.BridgeWindowOverlap
import Sude.PackedReachablePrimeDiagonal
import Sude.FC2KT75AnalyticSupply
import Sude.FC2KPoolMeanBounds

/-!
# FC2K Bridge Overlap & Multi-Scale Diagonal Prime Helpers

1. `bridgeLowGeometricOverlap_card_le_one` and `bridgeHighGeometricOverlap_card_le_one`:
   At every preterminal bridge stage `j` (`bridgeIteration X R₀ j < X`), at most one earlier
   bridge stage (`j - 1`) geometrically overlaps stage `j` on either side.
2. `odd_prime_in_interval_all_scales`:
   Combines `BMORFiniteTheta` (`hi ≤ 4 * 10 ^ 13`) and `bmor_theta_mod_two_all_ge_7e12`
   (`4 * 10 ^ 13 < hi`) to produce an odd prime in `(lo, hi]` whenever `5 * 10 ^ 10 ≤ lo`,
   `hi / 2 ≤ lo`, and `lo + hi / 10000 ≤ hi`.
-/

namespace Sude

noncomputable section

open scoped BigOperators

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-- If `bridgeIteration X R₀ (k + 2) < X`, then `bridgeIteration X R₀ k < (28 / 100) * X`
and `bridgeLowEnd X (bridgeIteration X R₀ j) ≤ bridgeLowStart X (bridgeIteration X R₀ i)`
for all `i ≤ k` and `k + 2 ≤ j` with `bridgeIteration X R₀ j < X`. -/
private theorem bridgeIteration_nonadjacent_separated {X R₀ : ℝ}
    (hX : 0 < X) (hR₀ : 0 < R₀) {i j : ℕ}
    (hij : i + 2 ≤ j) (hj : bridgeIteration X R₀ j < X) :
    bridgeLowEnd X (bridgeIteration X R₀ j) ≤ bridgeLowStart X (bridgeIteration X R₀ i) ∧
      bridgeHighEnd X (bridgeIteration X R₀ i) ≤ bridgeHighStart X (bridgeIteration X R₀ j) := by
  have hmono := bridgeIteration_mono X R₀ hX hR₀
  have hk2_le_j : i + 2 ≤ j := hij
  have hR_i2_lt : bridgeIteration X R₀ (i + 2) < X :=
    lt_of_le_of_lt (hmono hk2_le_j) hj
  have hR_i1_pos : 0 < bridgeIteration X R₀ (i + 1) :=
    bridgeIteration_pos X R₀ hX hR₀ (i + 1)
  have hR_i_pos : 0 < bridgeIteration X R₀ i :=
    bridgeIteration_pos X R₀ hX hR₀ i
  have hR_i1_lt : bridgeIteration X R₀ (i + 1) < X :=
    lt_of_le_of_lt (bridgeNext_ge X _ hX hR_i1_pos) hR_i2_lt
  have hstep1 : bridgeIteration X R₀ (i + 2) =
      bridgeIteration X R₀ (i + 1) + bridgeGapLower X (bridgeIteration X R₀ (i + 1)) := by
    change bridgeNext X (bridgeIteration X R₀ (i + 1)) = _
    rw [bridgeNext, if_pos hR_i1_lt]
  have hR_i1_53 : bridgeIteration X R₀ (i + 1) < (53 / 100 : ℝ) * X := by
    by_cases hhalf1 : X / 2 ≤ bridgeIteration X R₀ (i + 1)
    · have hsp1 : bridgeSpan X (bridgeIteration X R₀ (i + 1)) = X / 2 :=
        min_eq_right hhalf1
      have hg1 : bridgeGapLower X (bridgeIteration X R₀ (i + 1)) = (47 / 100 : ℝ) * X := by
        unfold bridgeGapLower bridgeWidth
        rw [hsp1]; ring
      linarith [hR_i2_lt, hstep1, hg1]
    · linarith
  have hR_i_lt : bridgeIteration X R₀ i < X :=
    lt_of_le_of_lt (bridgeNext_ge X _ hX hR_i_pos) hR_i1_lt
  have hstep0 : bridgeIteration X R₀ (i + 1) =
      bridgeIteration X R₀ i + bridgeGapLower X (bridgeIteration X R₀ i) := by
    change bridgeNext X (bridgeIteration X R₀ i) = _
    rw [bridgeNext, if_pos hR_i_lt]
  have hR_i_lt_half : bridgeIteration X R₀ i < X / 2 := by
    apply lt_of_not_ge
    intro hge
    have hsp0 : bridgeSpan X (bridgeIteration X R₀ i) = X / 2 := min_eq_right hge
    have hg0 : bridgeGapLower X (bridgeIteration X R₀ i) = (47 / 100 : ℝ) * X := by
      unfold bridgeGapLower bridgeWidth
      rw [hsp0]; ring
    linarith [hR_i1_53, hstep0, hg0]
  have hsp_i : bridgeSpan X (bridgeIteration X R₀ i) = bridgeIteration X R₀ i :=
    min_eq_left (le_of_lt hR_i_lt_half)
  have hR_i1_eq : bridgeIteration X R₀ (i + 1) = (194 / 100 : ℝ) * bridgeIteration X R₀ i := by
    rw [hstep0]
    unfold bridgeGapLower bridgeWidth
    rw [hsp_i]; ring
  have hR_i_28 : bridgeIteration X R₀ i < (28 / 100 : ℝ) * X := by
    linarith [hR_i1_53, hR_i1_eq]
  by_cases hhalf_j : bridgeIteration X R₀ j ≤ X / 2
  · have hR_i1_le_half : bridgeIteration X R₀ (i + 1) ≤ X / 2 :=
      le_trans (hmono (by omega : i + 1 ≤ j)) hhalf_j
    have hsp_i1 : bridgeSpan X (bridgeIteration X R₀ (i + 1)) = bridgeIteration X R₀ (i + 1) :=
      min_eq_left hR_i1_le_half
    have hR_i2_eq : bridgeIteration X R₀ (i + 2) =
        (194 / 100 : ℝ) * bridgeIteration X R₀ (i + 1) := by
      rw [hstep1]
      unfold bridgeGapLower bridgeWidth
      rw [hsp_i1]; ring
    have hR_j_ge : (194 / 100 : ℝ) * ((194 / 100 : ℝ) * bridgeIteration X R₀ i) ≤
        bridgeIteration X R₀ j := by
      have hm := hmono hk2_le_j
      linarith [hR_i2_eq, hR_i1_eq, hm]
    have hsp_j : bridgeSpan X (bridgeIteration X R₀ j) = bridgeIteration X R₀ j :=
      min_eq_left hhalf_j
    simp only [bridgeLowEnd, bridgeLowStart, bridgeHighEnd, bridgeHighStart, bridgeWidth,
      hsp_i, hsp_j]
    exact ⟨by linarith, by linarith⟩
  · have hhalf_j' : X / 2 < bridgeIteration X R₀ j := lt_of_not_ge hhalf_j
    have hsp_j : bridgeSpan X (bridgeIteration X R₀ j) = X / 2 :=
      min_eq_right (le_of_lt hhalf_j')
    simp only [bridgeLowEnd, bridgeLowStart, bridgeHighEnd, bridgeHighStart, bridgeWidth,
      hsp_i, hsp_j]
    exact ⟨by linarith, by linarith⟩

/-- At any preterminal bridge stage `j`, at most one prior lower window overlaps stage `j`. -/
theorem bridgeLowGeometricOverlap_card_le_one {X R₀ : ℝ}
    (hX : 0 < X) (hR₀ : 0 < R₀) {j : ℕ}
    (hj : bridgeIteration X R₀ j < X) :
    (bridgeLowGeometricOverlap X (bridgeIteration X R₀) j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have ha_lt : a < j := Finset.mem_range.mp ha'.1
  have hb_lt : b < j := Finset.mem_range.mp hb'.1
  have ha_not2 : ¬ (a + 2 ≤ j) := by
    intro h2
    have hsep := (bridgeIteration_nonadjacent_separated hX hR₀ h2 hj).1
    linarith [ha'.2.1]
  have hb_not2 : ¬ (b + 2 ≤ j) := by
    intro h2
    have hsep := (bridgeIteration_nonadjacent_separated hX hR₀ h2 hj).1
    linarith [hb'.2.1]
  omega

/-- At any preterminal bridge stage `j`, at most one prior upper window overlaps stage `j`. -/
theorem bridgeHighGeometricOverlap_card_le_one {X R₀ : ℝ}
    (hX : 0 < X) (hR₀ : 0 < R₀) {j : ℕ}
    (hj : bridgeIteration X R₀ j < X) :
    (bridgeHighGeometricOverlap X (bridgeIteration X R₀) j).card ≤ 1 := by
  apply Finset.card_le_one.mpr
  intro a ha b hb
  have ha' := Finset.mem_filter.mp ha
  have hb' := Finset.mem_filter.mp hb
  have ha_lt : a < j := Finset.mem_range.mp ha'.1
  have hb_lt : b < j := Finset.mem_range.mp hb'.1
  have ha_not2 : ¬ (a + 2 ≤ j) := by
    intro h2
    have hsep := (bridgeIteration_nonadjacent_separated hX hR₀ h2 hj).2
    linarith [ha'.2.2]
  have hb_not2 : ¬ (b + 2 ≤ j) := by
    intro h2
    have hsep := (bridgeIteration_nonadjacent_separated hX hR₀ h2 hj).2
    linarith [hb'.2.2]
  omega

/-- Positive `thetaAP` increment on `(lo, hi]` yields an odd prime `p` with `lo < p ≤ hi`. -/
private theorem exists_odd_prime_of_thetaAP_two_lt {lo hi : ℝ}
    (hlo : 2 < lo) (hhi : lo ≤ hi)
    (hinc : thetaAP lo 2 1 < thetaAP hi 2 1) :
    ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ lo < (p : ℝ) ∧ (p : ℝ) ≤ hi := by
  rw [thetaAP_eq_sum_apPrefix, thetaAP_eq_sum_apPrefix] at hinc
  have hlo0 : 0 ≤ lo := by linarith
  have hhi0 : 0 ≤ hi := by linarith
  have hsub : apPrefix lo 2 1 ⊆ apPrefix hi 2 1 := by
    intro p hp
    have hp' := (mem_apPrefix_iff lo 2 1 hlo0 p).mp hp
    exact (mem_apPrefix_iff hi 2 1 hhi0 p).mpr ⟨hp'.1, hp'.2.1.trans hhi, hp'.2.2⟩
  have hpos_sdiff : 0 < ∑ p ∈ apPrefix hi 2 1 \ apPrefix lo 2 1, Real.log p := by
    have hsplit := Finset.sum_sdiff hsub (f := fun p : ℕ => Real.log p)
    linarith
  have hne : (apPrefix hi 2 1 \ apPrefix lo 2 1).Nonempty := by
    by_contra hempty
    rw [Finset.not_nonempty_iff_eq_empty] at hempty
    rw [hempty, Finset.sum_empty] at hpos_sdiff
    linarith
  obtain ⟨p, hp⟩ := hne
  have ⟨hphi, hpnlo⟩ := Finset.mem_sdiff.mp hp
  have ⟨hp_prime, hp_le_hi, hp_mod⟩ := (mem_apPrefix_iff hi 2 1 hhi0 p).mp hphi
  have hp_gt_lo : lo < (p : ℝ) := by
    apply lt_of_not_ge
    intro hle
    exact hpnlo ((mem_apPrefix_iff lo 2 1 hlo0 p).mpr ⟨hp_prime, hle, hp_mod⟩)
  have hp_ne_two : p ≠ 2 := by
    intro rfl
    push_cast at hp_gt_lo
    linarith
  have hp_odd : Odd p := Nat.odd_iff.mpr (hp_prime.eq_two_or_odd.resolve_left hp_ne_two)
  exact ⟨p, hp_prime, hp_odd, hp_gt_lo, hp_le_hi⟩

/-- Multi-scale odd prime existence on `(lo, hi]` covering both `hi ≤ 4 * 10 ^ 13`
(via `BMORFiniteTheta` mod 4) and `hi > 4 * 10 ^ 13` (via `bmor_theta_mod_two_all_ge_7e12`). -/
theorem odd_prime_in_interval_all_scales
    (bmor : BMORFiniteTheta) (imp : BMORExplicitFormulaImports)
    {lo hi : ℝ}
    (hlo_min : (5 * 10 ^ 10 : ℝ) ≤ lo)
    (hlo_half : hi / 2 ≤ lo)
    (hwidth : lo + hi / 10000 ≤ hi) :
    ∃ p : ℕ, Nat.Prime p ∧ Odd p ∧ lo < (p : ℝ) ∧ (p : ℝ) ≤ hi := by
  have hhi_pos : 0 < hi := by linarith
  have hlo_le_hi : lo ≤ hi := by linarith
  by_cases hcap : hi ≤ (4 * 10 ^ 13 : ℝ)
  · have hlo1 : (1 : ℝ) ≤ lo := by linarith
    have hhi1 : (1 : ℝ) ≤ hi := by linarith
    have h1 := bmor_theta_two_via_four bmor lo hlo1 (hlo_le_hi.trans hcap)
    have h2 := bmor_theta_two_via_four bmor hi hhi1 hcap
    have hslo : Real.sqrt lo ≤ Real.sqrt hi := Real.sqrt_le_sqrt hlo_le_hi
    have hs_ge : (223606 : ℝ) ≤ Real.sqrt hi := by
      have hsq : (223606 : ℝ) ^ 2 ≤ hi := by
        linarith [show (223606 : ℝ) ^ 2 ≤ 5 * 10 ^ 10 by norm_num]
      rw [← Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 223606)]
      exact Real.sqrt_le_sqrt hsq
    have hsqrt_le : Real.sqrt hi ≤ hi / 223606 := by
      have hmul : (223606 : ℝ) * Real.sqrt hi ≤ Real.sqrt hi * Real.sqrt hi :=
        mul_le_mul_of_nonneg_right hs_ge (Real.sqrt_nonneg hi)
      rw [Real.mul_self_sqrt hhi_pos.le] at hmul
      linarith
    have h1_lo := (abs_le.mp h1).2
    have h2_lo := (abs_le.mp h2).1
    have hinc : thetaAP lo 2 1 < thetaAP hi 2 1 := by
      linarith
    exact exists_odd_prime_of_thetaAP_two_lt (by linarith) hlo_le_hi hinc
  · have hcap' : (4 * 10 ^ 13 : ℝ) < hi := lt_of_not_ge hcap
    have hlo_7e12 : (7 * 10 ^ 12 : ℝ) ≤ lo := by linarith
    have hhi_7e12 : (7 * 10 ^ 12 : ℝ) ≤ hi := by linarith
    have h1 := bmor_theta_mod_two_all_ge_7e12 imp hlo_7e12
    have h2 := bmor_theta_mod_two_all_ge_7e12 imp hhi_7e12
    have h1_hi := (abs_le.mp h1).2
    have h2_lo := (abs_le.mp h2).1
    have hinc : thetaAP lo 2 1 < thetaAP hi 2 1 := by
      linarith
    exact exists_odd_prime_of_thetaAP_two_lt (by linarith) hlo_le_hi hinc

end

end Sude
