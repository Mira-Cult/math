import Sude.FWEarlyReservationCard

/-! The FW10 early reservation invoice fits total square-cell capacity. -/
namespace Sude
noncomputable section

/-- The source's early budget is no larger than the total number of cells
throughout the FW lower-order range. All division is natural division. -/
theorem fwEarlyBudget_le_square {n : ℕ} (hn : 19485 ≤ n) :
    fwEarlyBudget n ≤ n * n := by
  have hdiv := Nat.div_mul_le_self n 450
  have hstage : 100 * (21 + 3 * (n / 450)) ≤ n := by omega
  have hfirst : 12 * (n + 8) ≤ 24 * n := by omega
  have hprod := Nat.mul_le_mul hfirst hstage
  unfold fwEarlyBudget
  nlinarith

/-- Supplied five bridge batches and a retained set with the source sizes
leave enough total cells for all source-counted wide block endpoints. No
existence or row/column/diagonal geometry is asserted. -/
theorem fw_early_protected_values_fit {n : ℕ} (hn : 19485 ≤ n)
    (batches : ℕ → List DoublePair)
    (hlen : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16) :
    4 * (3 * (n / 450) * (3 * (n + 8))) +
      (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained).card ≤ n * n := by
  have h := fw_early_reservation_card_budget n batches hlen retained
    (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained) hretained
    (Finset.Subset.refl _)
  have hs := fwEarlyBudget_le_square hn
  omega

end
end Sude
