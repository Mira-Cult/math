import Sude.FWStageVaryingBridgeGrid
import Sude.FWPermutedWideGapBounds
import Sude.FWWidePhysicalGrid

/-! Conditional abstract bridge-plus-wide grid using stage-permuted source
gaps and recomputed radii. No physical orientation or theta claim is made. -/

namespace Sude
noncomputable section

/-- Starting with a supplied even grid that has crossed X/23, append the
stage-permuted bridge and wide source gaps. Both radii are recomputed from
the actual selected gaps. No physical orientation is asserted. -/
theorem fw_permuted_bridge_wide_source_grid {α : Type*} [DecidableEq α] {n : ℕ}
    (reserved : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n reserved batches j)
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (destination : Fin (3 * (n + 8)))
    (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ)
    (hgrid : CompleteEvenGrid initial initialGap radius) (heven : 2 ∣ radius)
    (hcross : (poolMaximum n : ℝ) / 23 ≤ radius)
    (μ : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ μ)
    (hmhi : μ ≤ (123 / 250 : ℝ) * poolMaximum n)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))) :
    let index := fwPermutedBridgeIndex πb destination
    let bridgeGap := fwStageVaryingJoinedBridgeGap initialGap batches index
    let bridgeLabels := initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
      (Finset.range 5).image (Sum.inr : ℕ → Sum α ℕ)
    let bridgeRadius := radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches (index j) j
    let wideGap := fun j => fwPermutedWideSourceGap blocks hlen πw j destination
    CompleteEvenGrid bridgeLabels bridgeGap bridgeRadius ∧
      2 ∣ bridgeRadius ∧ (poolMaximum n : ℝ) ≤ bridgeRadius ∧
      (∀ j, 0 < wideGap j ∧ 2 ∣ wideGap j ∧
        (2 / 3 : ℝ) * poolMaximum n ≤ (wideGap j : ℝ) ∧ (wideGap j : ℝ) < poolMaximum n) ∧
      CompleteEvenGrid
        (bridgeLabels.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
          (Finset.univ : Finset (Fin (3 * (n / 450)))).map ⟨Sum.inr, Sum.inr_injective⟩)
        (Sum.elim bridgeGap wideGap : Sum (Sum α ℕ) (Fin (3 * (n / 450))) → ℕ)
        (bridgeRadius + ∑ j, wideGap j) ∧
      2 ∣ bridgeRadius + ∑ j, wideGap j ∧
      (2 : ℝ) * (n / 450 : ℕ) * poolMaximum n ≤ ∑ j, (wideGap j : ℝ) := by
  classical
  dsimp only
  let index := fwPermutedBridgeIndex πb destination
  let bridgeGap := fwStageVaryingJoinedBridgeGap initialGap batches index
  let bridgeLabels := initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
    (Finset.range 5).image (Sum.inr : ℕ → Sum α ℕ)
  let bridgeRadius := radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches (index j) j
  let wideGap := fun j => fwPermutedWideSourceGap blocks hlen πw j destination
  have hb := fw_permuted_bridge_batches_grow_grid n reserved batches hvalid πb destination
    initial initialGap radius hgrid heven hcross
  have hbgrid : CompleteEvenGrid bridgeLabels bridgeGap bridgeRadius := hb.1
  have hbcover : (poolMaximum n : ℝ) ≤ bridgeRadius := hb.2
  have hbsum : 2 ∣ ∑ j ∈ Finset.range 5, selectedBridgeGap batches (index j) j := by
    apply Finset.dvd_sum
    intro j hj
    exact (fw_selected_bridge_gap_bounds n reserved batches hvalid _ j (Finset.mem_range.mp hj)).1
  have hbeven : 2 ∣ bridgeRadius := dvd_add heven hbsum
  have hw (j : Fin (3 * (n / 450))) : 0 < wideGap j ∧ 2 ∣ wideGap j ∧
      (2 / 3 : ℝ) * poolMaximum n ≤ (wideGap j : ℝ) ∧ (wideGap j : ℝ) < poolMaximum n :=
    fw_permuted_wide_source_gap_bounds μ (poolMaximum n) hX hmlo hmhi blocks hlen hmatched πw j destination
  have hwbounded : ∀ j ∈ (Finset.univ : Finset (Fin (3 * (n / 450)))),
      2 ∣ wideGap j ∧ wideGap j ≤ bridgeRadius := by
    intro j _
    refine ⟨(hw j).2.1, ?_⟩
    have hreal : (wideGap j : ℝ) ≤ bridgeRadius := (le_of_lt (hw j).2.2.2).trans hbcover
    exact_mod_cast hreal
  have hfinal := fw_wide_family_grid bridgeLabels bridgeGap wideGap bridgeRadius hbgrid hbeven
    Finset.univ hwbounded
  have hsum : (∑ _j : Fin (3 * (n / 450)), (2 / 3 : ℝ) * poolMaximum n) ≤
      ∑ j, (wideGap j : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact (hw j).2.2.1
  have htotal : (2 : ℝ) * (n / 450 : ℕ) * poolMaximum n ≤ ∑ j, (wideGap j : ℝ) := by
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
    push_cast at hsum
    nlinarith
  exact ⟨hbgrid, hbeven, hbcover, hw, hfinal.1, hfinal.2, htotal⟩

end
end Sude
