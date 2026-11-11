import Sude.FWPhysicalSharpBudget
import Sude.FWEarlyReservationCard

/-! Physical FW supply from supplied actual early-reservation sets. -/
namespace Sude
noncomputable section

/-- Five supplied bridge batches and a supplied retained-seed set pay the
FW10 early reservation budget for the source number of wide blocks. This
does not establish that those witnesses exist or identify physical cells
with their values; the caller supplies the remaining cell conditions. -/
theorem fw_reflected_supply_with_counted_early_reservations {n : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair)
    (hlenBridge : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained removed : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (hremoved : removed ⊆ priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin (3 * (n / 450) * (3 * (n + 8))) × Fin 4 → Cell n)
    (reserved : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reserved)
    (hreserved : ∀ c ∈ reserved, entry a c ∈ removed) :
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450) * (3 * (n + 8)))) (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint removed) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ reserved, entry a' cell = entry a cell) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks a'
        (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a' (cells (Fin.cast hlen i, 1)) = entry a' (cells (Fin.cast hlen i, 0)) + gap ∧
        entry a' (cells (Fin.cast hlen i, 2)) = entry a' (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  have hbudget := fw_early_reservation_card_budget n batches hlenBridge retained removed hretained hremoved
  exact fw_reflected_supply_with_sharp_early_budget_and_even_gaps bmor upper lower sharp hnlo hnhi m hmlo hmhi
    removed hbudget a cells reserved hcells hnew hreserved

end
end Sude
