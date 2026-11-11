import Sude.FWPhysicalExactReservations
import Sude.FWEarlyBudgetCapacity
import Sude.ProtectedPoolCapacity

/-! FW wide supply preserving every supplied early pool value in place. -/
namespace Sude
noncomputable section

/-- Under the stated analytic, mean and supplied-set assumptions, total
capacity provides injective free cells and physically installs the selected
wide blocks. Every supplied early value that belongs to the pool remains at
its original cell. This does not establish the bridge or seed witnesses, nor
any row, column, diagonal or FW rectangle geometry for the selected cells. -/
theorem fw_reflected_supply_with_protected_early_values {n : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp)
    (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (m : ℝ)
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair)
    (hlenBridge : ∀ j < 5, (batches j).length = 3 * (n + 8))
    (retained : Finset ℕ)
    (hretained : retained.card = 2 * (6 * (n + 8)) * 16)
    (a : Cell n ≃ Fin (n * n)) :
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (cells : Fin (3 * (n / 450) * (3 * (n + 8))) × Fin 4 → Cell n),
      Function.Injective cells ∧
      (∀ x, cells x ∉ protectedPoolCells a (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
    ∃ (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450) * (3 * (n + 8)))) (a' : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained)) ∧
      (∀ x : Fin blocks.length × Fin 4,
        entry a' (cells (Fin.cast hlen x.1, x.2)) = doublePairSequenceEndpoint blocks x) ∧
      (∀ cell ∈ protectedPoolCells a (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained),
        entry a' cell = entry a cell) ∧
      fwInstalledPairBounds m (poolMaximum n) blocks a'
        (fun x => cells (Fin.cast hlen x.1, x.2)) ∧
      (∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry a' (cells (Fin.cast hlen i, 1)) = entry a' (cells (Fin.cast hlen i, 0)) + gap ∧
        entry a' (cells (Fin.cast hlen i, 2)) = entry a' (cells (Fin.cast hlen i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) ∧
      (∀ p ∈ (priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained),
        ∀ hp : p ∈ pool n, entry a' ((entryPool a).symm ⟨p, hp⟩) = p) := by
  let values := priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained
  have hcapacity := fw_early_protected_values_fit hnlo batches hlenBridge retained hretained
  obtain ⟨cells, hcells, hnew⟩ := protectedPoolCells_free_cells_of_card a values hcapacity
  have hreserved : ∀ c ∈ protectedPoolCells a values, entry a c ∈ values := by
    intro c hc
    exact (mem_protectedPoolCells a values c).mp hc
  obtain ⟨blocks, hlen, a', hmatched, hpair, havoid, hplaced, hfixed, hbounds, hgap⟩ :=
    fw_reflected_supply_avoiding_all_early_values bmor upper lower sharp hnlo hnhi m hmlo hmhi
      batches hlenBridge retained hretained a cells (protectedPoolCells a values) hcells hnew hreserved
  refine ⟨cells, hcells, hnew, blocks, hlen, a', hmatched, hpair, havoid, hplaced, hfixed, hbounds, hgap, ?_⟩
  intro p hp hpPool
  exact protectedPoolCells_preserve_value a a' values p hp hpPool hfixed

end
end Sude
