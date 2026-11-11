import Sude.FWPermutedWideGapBounds
import Sude.FWStageVaryingBridgeGrid

/-! Numerical lower bound for the radius recomputed from actual
stage-permuted source gaps. No physical grid or flow is constructed. -/
namespace Sude
noncomputable section

/-- The matched wide blocks alone supply the required total gap. This holds
for every destination block and stage-wise permutation. -/
theorem fw_permuted_wide_gap_total_lower {n : ℕ}
    (μ : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ μ)
    (hmhi : μ ≤ (123 / 250 : ℝ) * poolMaximum n)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n))))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (destination : Fin (3 * (n + 8))) :
    2 * ((n / 450) * poolMaximum n) ≤ ∑ j, fwPermutedWideSourceGap blocks hlen πw j destination := by
  have hsum : (∑ _j : Fin (3 * (n / 450)), (2 / 3 : ℝ) * poolMaximum n) ≤
      ∑ j, (fwPermutedWideSourceGap blocks hlen πw j destination : ℝ) := by
    apply Finset.sum_le_sum
    intro j _
    exact (fw_permuted_wide_source_gap_bounds μ (poolMaximum n) hX hmlo hmhi blocks hlen hmatched πw j destination).2.2.1
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  push_cast at hsum
  have hreal : (2 : ℝ) * ((n / 450 : ℕ) : ℝ) * (poolMaximum n : ℝ) ≤
      ∑ j, (fwPermutedWideSourceGap blocks hlen πw j destination : ℝ) := by nlinarith
  have hn : 2 * (n / 450) * poolMaximum n ≤ ∑ j, fwPermutedWideSourceGap blocks hlen πw j destination := by
    exact_mod_cast hreal
  simpa [Nat.mul_assoc] using hn

/-- The recomputed bridge-plus-wide radius dominates the wide-gap total;
therefore it meets the numeric capacity for every actual edge destination.
The initial radius and all bridge increments are natural numbers. -/
theorem fw_permuted_radius_capacity {n : ℕ}
    (μ : ℝ) (hX : (100 : ℝ) ≤ poolMaximum n)
    (hmlo : (243 / 500 : ℝ) * poolMaximum n ≤ μ)
    (hmhi : μ ≤ (123 / 250 : ℝ) * poolMaximum n)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (hmatched : ∀ block ∈ blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft μ (poolMaximum n)) (fwReflectedRight μ (poolMaximum n))))
    (πw : Fin (3 * (n / 450)) → Equiv.Perm (Fin (3 * (n + 8))))
    (πb : Fin 5 → Equiv.Perm (Fin (3 * (n + 8))))
    (batches : ℕ → List DoublePair) (radius : ℕ) (edge : Fin 3 × Fin n) :
    let destination : Fin (3 * (n + 8)) := bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge
    2 * ((n / 450) * poolMaximum n) ≤
      radius + (∑ j ∈ Finset.range 5, selectedBridgeGap batches (fwPermutedBridgeIndex πb destination j) j) +
        ∑ j, fwPermutedWideSourceGap blocks hlen πw j destination := by
  dsimp only
  have h := fw_permuted_wide_gap_total_lower μ hX hmlo hmhi blocks hlen hmatched πw
    (bridgeOrdinaryBlockIndex (r := 3) (d := 6) (by omega) edge)
  omega

end
end Sude
