import Sude.FWBridgeGeometry

/-! Source-width FW bridge batch selection from explicit paid stocks. -/
namespace Sude
noncomputable section

/-- Under explicit actual pool membership, source-window, side-stock,
deletion and square-gate hypotheses, select `k` disjoint FW bridge blocks.
Their shared gaps are positive even natural numbers in the source interval.
The stock gates, prior deletion budgets and the existence of any particular
batch are not asserted independently of these hypotheses. -/
theorem fw_bridge_select_pool_blocks {n : ℕ} (X R : ℝ) (hX : 0 < X) (hR : 0 < R)
    (low high removedLow removedHigh : Finset ℕ) (M k : ℕ)
    (hpoolLow : ∀ a ∈ low, a ∈ pool n) (hpoolHigh : ∀ b ∈ high, b ∈ pool n)
    (hlowWindow : ∀ a ∈ low,
      fwBridgeLowStart X R < (a : ℝ) ∧ (a : ℝ) ≤ fwBridgeLowEnd X R)
    (hhighWindow : ∀ b ∈ high,
      fwBridgeHighStart X R < (b : ℝ) ∧ (b : ℝ) ≤ fwBridgeHighEnd X R)
    (hlow : M + 2 * k + removedLow.card ≤ low.card)
    (hhigh : M + 2 * k + removedHigh.card ≤ high.card)
    (hgate : fwBridgeWidth X R + 1 < (M : ℝ) * M) :
    ∃ blocks : List DoublePair, blocks.length = k ∧
      (∀ b ∈ blocks, b.valid (low \ removedLow) (high \ removedHigh)) ∧
      blocks.Pairwise (fun b c => Disjoint b.footprint c.footprint) ∧
      (∀ b ∈ blocks, 0 < b.high₁ - b.low₁ ∧ 2 ∣ b.high₁ - b.low₁ ∧
        (208 / 231 : ℝ) * bridgeSpan X R < ((b.high₁ - b.low₁ : ℕ) : ℝ) ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) < bridgeSpan X R ∧
        ((b.high₁ - b.low₁ : ℕ) : ℝ) ≤ R) := by
  have hgeom := fw_bridge_window_geometry X R hX hR
  have horder : ∀ a ∈ low, ∀ b ∈ high, a < b := by
    intro a ha b hb
    exact (fw_bridge_cross_gap X R hX hR a b (hlowWindow a ha) (hhighWindow b hb)).1
  have hspan : ∀ a ∈ low, ∀ b ∈ high,
      fwBridgeGapLower X R < ((b - a : ℕ) : ℝ) ∧
        ((b - a : ℕ) : ℝ) ≤ fwBridgeGapLower X R + 2 * fwBridgeWidth X R := by
    intro a ha b hb
    have h := fw_bridge_cross_gap X R hX hR a b (hlowWindow a ha) (hhighWindow b hb)
    have heq : fwBridgeGapLower X R + 2 * fwBridgeWidth X R = bridgeSpan X R := by
      simp only [fwBridgeGapLower]
      ring
    exact ⟨h.2.2.1, by rw [heq]; exact le_of_lt h.2.2.2.1⟩
  obtain ⟨blocks, hlen, hvalid, hpair⟩ :=
    select_pool_double_pairs_fc2k low high removedLow removedHigh M k
      (fwBridgeGapLower X R) (fwBridgeWidth X R) hpoolLow hpoolHigh horder hspan
      hlow hhigh (le_of_lt hgeom.1) hgate
  refine ⟨blocks, hlen, hvalid, hpair, ?_⟩
  intro b hb
  have hv := hvalid b hb
  have hl := (Finset.mem_sdiff.mp hv.1).1
  have hh := (Finset.mem_sdiff.mp hv.2.2.1).1
  have hg := fw_bridge_cross_gap X R hX hR b.low₁ b.high₁ (hlowWindow _ hl) (hhighWindow _ hh)
  have heven := fw_bridge_pool_gap_even X R hX hR (hpoolLow _ hl) (hpoolHigh _ hh)
    (hlowWindow _ hl) (hhighWindow _ hh)
  have hcoef := (fw_bridge_width_and_increment X R).2
  exact ⟨hg.2.1, heven, by rw [← hcoef]; exact hg.2.2.1, hg.2.2.2.1, hg.2.2.2.2⟩

end
end Sude
