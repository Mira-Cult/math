import Sude.FWMatchedBlockGeometry
import Sude.BridgeDepletion

namespace Sude
noncomputable section

/-- Matched reflected wide pairs lie outside the central quarter on both sides. -/
theorem fw_wide_batch_outside_quarter
    (m X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ) * X)
    (blocks : List DoublePair)
    (hmatched : ∀ b ∈ blocks, b.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X))) :
    (∀ p ∈ doubleBatchLow blocks, (p : ℝ) ≤ m - X / 4) ∧
      (∀ p ∈ doubleBatchHigh blocks, m + X / 4 ≤ (p : ℝ)) := by
  classical
  constructor
  · intro p hp
    simp only [doubleBatchLow, Finset.mem_biUnion, List.mem_toFinset,
      Finset.mem_insert, Finset.mem_singleton] at hp
    obtain ⟨b, hb, hp⟩ := hp
    obtain ⟨hm₁, hg₁, _, hm₂, hg₂, _⟩ :=
      fw_matched_block_pair_bounds m X hX hmlo hmhi b (hmatched b hb)
    rw [abs_le] at hm₁ hm₂
    rcases hp with rfl | rfl <;> linarith
  · intro p hp
    simp only [doubleBatchHigh, Finset.mem_biUnion, List.mem_toFinset,
      Finset.mem_insert, Finset.mem_singleton] at hp
    obtain ⟨b, hb, hp⟩ := hp
    obtain ⟨hm₁, hg₁, _, hm₂, hg₂, _⟩ :=
      fw_matched_block_pair_bounds m X hX hmlo hmhi b (hmatched b hb)
    rw [abs_le] at hm₁ hm₂
    rcases hp with rfl | rfl <;> linarith

/-- The entire wide value batch is shielded for any nonnegative margin. -/
theorem fw_wide_batch_shielded
    (m X w : ℝ) (hX : 100 ≤ X) (hw : 0 ≤ w)
    (hmlo : (243 / 500 : ℝ) * X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ) * X)
    (blocks : List DoublePair)
    (hmatched : ∀ b ∈ blocks, b.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X))) :
    ∀ p ∈ doubleBatchLow blocks ∪ doubleBatchHigh blocks,
      (p : ℝ) ≤ m - X / 4 + w * X ∨ m + X / 4 - w * X ≤ (p : ℝ) := by
  have h := fw_wide_batch_outside_quarter m X hX hmlo hmhi blocks hmatched
  have hwX : 0 ≤ w * X := mul_nonneg hw (by linarith)
  intro p hp
  rcases Finset.mem_union.mp hp with hp | hp
  · left; have hh := h.1 p hp; linarith
  · right; have hh := h.2 p hp; linarith

end
end Sude
