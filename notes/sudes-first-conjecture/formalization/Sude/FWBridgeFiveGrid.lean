import Sude.FWBridgeFiveEmpty
import Sude.FWBridgeGridGrowth

/-! Five selected FW bridge batches extend every supplied abstract even grid. -/
namespace Sude
noncomputable section

/-- With the explicit published BMOR and RS inputs, one set of five actual
nominal FW batches has the sequential/disjointness/cardinality properties
and works for every block index and every supplied labelled even grid that
already covers `X/23`: the resulting abstract grid covers `X`. Labels use
a disjoint sum. This theorem gives no simultaneous physical assignment,
row/column/diagonal geometry, or initial-grid construction. -/
theorem bmor_fw_five_bridge_batches_grow_every_grid
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    ∃ batches : ℕ → List DoublePair,
      (∀ j < 5, FWBridgeSequentialValid n ∅ batches j) ∧
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) ∧
      (∀ (α : Type) [DecidableEq α] (index : Fin (3 * (n + 8)))
        (initial : Finset α) (initialGap : α → ℕ) (radius : ℕ),
        CompleteEvenGrid initial initialGap radius → 2 ∣ radius →
        (poolMaximum n : ℝ) / 23 ≤ radius →
        CompleteEvenGrid
          (initial.map ⟨Sum.inl, Sum.inl_injective⟩ ∪
            (Finset.range 5).image (Sum.inr : ℕ → Sum α ℕ))
          (joinedBridgeGap initialGap batches index)
          (radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j) ∧
        (poolMaximum n : ℝ) ≤
          ((radius + ∑ j ∈ Finset.range 5, selectedBridgeGap batches index j : ℕ) : ℝ)) := by
  obtain ⟨batches, hvalid, hdisjoint, hcard⟩ :=
    bmor_fw_five_bridge_batches_empty bmor upper lower hnlo hnhi
  refine ⟨batches, hvalid, hdisjoint, hcard, ?_⟩
  intro α inst index initial initialGap radius hgrid heven hcoverage
  exact fw_selected_bridge_batches_grow_grid n ∅ batches hvalid index initial initialGap radius
    hgrid heven hcoverage

end
end Sude
