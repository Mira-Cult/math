import Sude.FWPhysicalCountedReservations

/-! Reserve the entire supplied FW10 bridge-and-seed value union. -/
namespace Sude
noncomputable section

/-- Each newly installed FW block avoids every value in the supplied bridge
and retained-seed union, while preserving the selected cells and geometric
bounds. This theorem assumes the supplied batch and retained-set properties;
it does not construct those sets or prove the cell mapping or controller. -/
theorem fw_reflected_supply_avoiding_all_early_values {n : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair)
    (hlenBridge : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (a : Cell n ≃ Fin (n * n)) (cells : Fin (3 * (n / 450) * (3 * (n + 8))) × Fin 4 → Cell n)
    (reserved : Finset (Cell n)) (hcells : Function.Injective cells)
    (hnew : ∀ x, cells x ∉ reserved)
    (hreserved : ∀ c ∈ reserved, entry a c ∈ (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) :
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450) * (3 * (n + 8)))) (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ reserved, entry a' cell = entry a cell) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks a'
        (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a' (cells (Fin.cast hlen i, 1)) = entry a' (cells (Fin.cast hlen i, 0)) + gap ∧
        entry a' (cells (Fin.cast hlen i, 2)) = entry a' (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  exact fw_reflected_supply_with_counted_early_reservations bmor upper lower sharp hnlo hnhi m hmlo hmhi
    batches hlenBridge retained (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)
    hretained (Finset.Subset.refl _) a cells reserved hcells hnew hreserved

end
end Sude
