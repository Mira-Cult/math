import Sude.BridgeDepletion
import Sude.FWEarlyBudgetMargin

/-! FW10 accounting for actual bridge-batch and retained-seed sets. -/
namespace Sude
noncomputable section

/-- Five supplied bridge batches of `3(n+8)` double blocks reserve at
most the FW10 bridge charge. This is a set-cardinality bound; it does not
assert the existence, validity, placement, or stock supply of these batches. -/
theorem fw_five_bridge_reservation_card_le (n : ℕ) (batches : ℕ → List DoublePair)
    (hlen : ∀ j < 5, (batches j).length = 3 * (n + 8)) :
    (priorBridgeReservation ∅ (Finset.range 5) batches).card ≤
      2 * (6 * (n + 8)) * 5 := by
  have hstage : ∀ j ∈ Finset.range 5,
      (doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j)).card ≤ 4 * (3 * (n + 8)) := by
    intro j hj
    have hl := doubleBatchLow_card_le (batches j)
    have hh := doubleBatchHigh_card_le (batches j)
    have hu := Finset.card_union_le (doubleBatchLow (batches j)) (doubleBatchHigh (batches j))
    rw [hlen j (Finset.mem_range.mp hj)] at hl hh
    omega
  have hc := Finset.card_biUnion_le_card_mul (Finset.range 5)
    (fun j => doubleBatchLow (batches j) ∪ doubleBatchHigh (batches j))
    (4 * (3 * (n + 8))) hstage
  have hbridge : (priorBridgeReservation ∅ (Finset.range 5) batches).card ≤
      5 * (4 * (3 * (n + 8))) := by
    simpa [priorBridgeReservation, stagedReservation] using hc
  nlinarith

/-- If the actual removed values are contained in the bridge and retained
seed sets, then the source's wide block count fits FW10's entire budget.
The 17th candidate stratum and later growth are not included. No hypotheses
here assert a bridge construction or identify reserved physical cells. -/
theorem fw_early_reservation_card_budget (n : ℕ) (batches : ℕ → List DoublePair)
    (hlen : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained removed : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (hremoved : removed ⊆ priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) :
    removed.card + 4 * (3 * (n / 450) * (3 * (n + 8))) ≤ fwEarlyBudget n := by
  have hb := fw_five_bridge_reservation_card_le n batches hlen
  have hu := Finset.card_union_le (priorBridgeReservation ∅ (Finset.range 5) batches) retained
  have hs := Finset.card_le_card hremoved
  unfold fwEarlyBudget
  nlinarith

end
end Sude
