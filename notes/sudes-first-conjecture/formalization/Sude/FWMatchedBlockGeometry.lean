import Sude.FWReflectedGeometry
import Sude.BMORMatchedBinInputs
import Sude.MatchedBinPreservedBatch

/-! Retain FW's midpoint and gap control for both pairs in each block. -/
namespace Sude
noncomputable section

/-- Each of a label-preserving block's two physical pairs satisfies the FW
reflected-bin midpoint and gap bounds, even when the pairs use different
bins. The mean interval remains an explicit internal hypothesis. -/
theorem fw_matched_block_pair_bounds (m X : ℝ) (hX : 100 ≤ X)
    (hmlo : (243 / 500 : ℝ) * X ≤ m) (hmhi : m ≤ (123 / 250 : ℝ) * X)
    (block : DoublePair)
    (hm : block.MatchedValid
      (bmorLowBins (fwReflectedLeft m X) (fwReflectedRight m X))
      (bmorHighBins (fwReflectedLeft m X) (fwReflectedRight m X))) :
    |((block.low₁ : ℝ) + block.high₁) / 2 - m| ≤ X / 235 ∧
      (2 / 3 : ℝ) * X ≤ (block.high₁ : ℝ) - block.low₁ ∧
      (block.high₁ : ℝ) - block.low₁ ≤
        (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X ∧
    |((block.low₂ : ℝ) + block.high₂) / 2 - m| ≤ X / 235 ∧
      (2 / 3 : ℝ) * X ≤ (block.high₂ : ℝ) - block.low₂ ∧
      (block.high₂ : ℝ) - block.low₂ ≤
        (2 * ((16 / 235 : ℝ) + 1 / 3) + 2 * (16 / 235 : ℝ)) * X := by
  obtain ⟨hends, _, _, hpairs⟩ := fw_reflected_bin_geometry m X hX hmlo hmhi
  obtain ⟨_, ⟨i, hli, hhi⟩, ⟨j, hlj, hhj⟩⟩ := hm
  have hli' := (mem_apInterval_iff _ _ 2 1 (by linarith [(hends (i, false)).1])
    (by linarith [(hends (i, false)).1, (hends (i, false)).2.1]) block.low₁).mp hli
  have hhi' := (mem_apInterval_iff _ _ 2 1 (by linarith [(hends (i, true)).1])
    (by linarith [(hends (i, true)).1, (hends (i, true)).2.1]) block.high₁).mp hhi
  have hlj' := (mem_apInterval_iff _ _ 2 1 (by linarith [(hends (j, false)).1])
    (by linarith [(hends (j, false)).1, (hends (j, false)).2.1]) block.low₂).mp hlj
  have hhj' := (mem_apInterval_iff _ _ 2 1 (by linarith [(hends (j, true)).1])
    (by linarith [(hends (j, true)).1, (hends (j, true)).2.1]) block.high₂).mp hhj
  exact ⟨(hpairs i block.low₁ block.high₁ hli'.2.1 hli'.2.2.1 hhi'.2.1 hhi'.2.2.1).1,
    (hpairs i block.low₁ block.high₁ hli'.2.1 hli'.2.2.1 hhi'.2.1 hhi'.2.2.1).2.1,
    (hpairs i block.low₁ block.high₁ hli'.2.1 hli'.2.2.1 hhi'.2.1 hhi'.2.2.1).2.2,
    (hpairs j block.low₂ block.high₂ hlj'.2.1 hlj'.2.2.1 hhj'.2.1 hhj'.2.2.1).1,
    (hpairs j block.low₂ block.high₂ hlj'.2.1 hlj'.2.2.1 hhj'.2.1 hhj'.2.2.1).2.1,
    (hpairs j block.low₂ block.high₂ hlj'.2.1 hlj'.2.2.1 hhj'.2.1 hhj'.2.2.1).2.2⟩

end
end Sude
