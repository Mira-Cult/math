import Sude.FWBridgeNumericalGates
import Sude.FWBridgeFiveSequential

/-! The five nominal FW bridge batches with an empty initial reservation. -/
namespace Sude
noncomputable section

/-- Under the explicit published BMOR and RS hypotheses, the fixed
`X / 30000` parameter pays all five nominal-stage gates when the initial
reservation is empty. The resulting actual batches carry cumulative
reservation validity and disjointness. This does not prove physical
placement, an actual grid, or any complete controller. -/
theorem bmor_fw_five_bridge_batches_empty
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) :
    ∃ batches : ℕ → List DoublePair,
      (∀ j < 5, FWBridgeSequentialValid n ∅ batches j) ∧
      (∀ i < 5, ∀ j < 5, i ≠ j →
        Disjoint (doubleBatchLow (batches i) ∪ doubleBatchHigh (batches i))
          (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))) ∧
      (∀ j ≤ 5, (priorBridgeReservation ∅ (Finset.range j) batches).card ≤
        (∅ : Finset ℕ).card + j * (4 * (3 * (n + 8)))) := by
  obtain ⟨hlow, hhigh, hgate⟩ := fw_bridge_empty_initial_gates upper lower hnlo hnhi
  exact bmor_fw_five_bridge_batches_sequential bmor upper n ∅ (fun _ => fwBridgeNumericalM n)
    (by omega) (by omega) hlow hhigh hgate

end
end Sude
