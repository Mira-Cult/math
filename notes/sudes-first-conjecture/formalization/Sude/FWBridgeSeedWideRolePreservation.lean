import Sude.FWBridgeSeedFullPlacement
import Sude.FWWideSupplyRoles
import Sude.ProtectedPoolCells

/-! A witness-dependent connector; the wide geometry is explicitly supplied. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

def fwBridgeSeedProtectedValues {n : ℕ} (batches : ℕ → List DoublePair)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) : Finset ℕ :=
  priorBridgeReservation ∅ (Finset.range 5) batches ∪
    retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub

/-- The square and witnesses can come from `bmor_fw_bridge_and_seed_full_placement`.
All their occurring reserved values remain in their original cells.  The base,
wide-layer layout, and avoidance are supplied after those witnesses are known. -/
theorem fw_select_wide_roles_preserving_bridge_seed {n L : ℕ}
    (bmor : BMORFiniteTheta) (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (m : ℝ) (_hmean : m = (Lucas.poolTotal n : ℝ) / (n * n : ℕ))
    (hmlo : (243 / 500 : ℝ) * (poolMaximum n : ℝ) ≤ m)
    (hmhi : m ≤ (123 / 250 : ℝ) * (poolMaximum n : ℝ))
    (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n ∅ batches j)
    (candidates : Finset ℕ) (hcard : candidates.card = 17 * (6 * (n + 8)))
    (kept : Finset ℕ) (hsub : kept ⊆ Finset.range 17) (hkept : kept.card = 16)
    (hinj : Function.Injective (sortedSeedEndpoint candidates 17 (6 * (n + 8)) 2 hcard))
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (a : Cell n ≃ Fin (n * n)) (base spatial : Finset (Cell n))
    (hrectbase : packedRectangleSupport hs choice ⊆ base)
    (hprior : protectedPoolCells a (fwBridgeSeedProtectedValues batches candidates hcard kept hsub) ⊆ base)
    (hdiagfree : ∀ x : Fin ((3 * (n / 450)) * (4 * 6)) × Fin 4,
      packedRectangleCorner hs choice (fwWideRectangle hwide x.1, x.2) ∉
        protectedPoolCells a (fwBridgeSeedProtectedValues batches candidates hcard kept hsub))
    (rows cols : List (LayerPacking.Layer n))
    (hr : rows.length = (3 * (n / 450)) * 3) (hc : cols.length = (3 * (n / 450)) * 3)
    (hrows : LayerPacking.PackedLayers base rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (base ∪ LayerPacking.layersSupport rows)) cols)
    (hdisjoint : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)))
    (hspatial : ∀ x, fwWidePhysicalCells hwide hs choice rows cols hr hc x ∉ spatial) :
    let low := bmorLowBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    let high := bmorHighBins (fwReflectedLeft m (poolMaximum n)) (fwReflectedRight m (poolMaximum n))
    ∃ (blocks : List DoublePair)
      (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
      (b : Cell n ≃ Fin (n * n)),
      (∀ block ∈ blocks, block.MatchedValid low high) ∧
      blocks.Pairwise (fun x y => Disjoint x.footprint y.footprint) ∧
      (∀ block ∈ blocks, Disjoint block.footprint
        (fwBridgeSeedProtectedValues batches candidates hcard kept hsub)) ∧
      (∀ c, entry a c ∈ fwBridgeSeedProtectedValues batches candidates hcard kept hsub →
        entry b c = entry a c) ∧
      (∀ x : FWWideInputs n,
        entry b (fwWidePhysicalCells hwide hs choice rows cols hr hc x) =
          doublePairSequenceEndpoint blocks
            (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) ∧
      (∀ x, fwWidePhysicalCells hwide hs choice rows cols hr hc x ∉ spatial) ∧
      (let cells : Fin blocks.length × Fin 4 → Cell n := fun x =>
        fwWidePhysicalCells hwide hs choice rows cols hr hc
          ((Equiv.ofBijective (fwWideFlatSlot n) (fwWideFlatSlot_bijective n)).symm
            (Fin.cast hlen x.1, x.2))
       fwInstalledPairBounds m (poolMaximum n) blocks b cells ∧
       ∀ i : Fin blocks.length, ∃ gap : ℕ, 0 < gap ∧ gap % 2 = 0 ∧
        entry b (cells (i, 1)) = entry b (cells (i, 0)) + gap ∧
        entry b (cells (i, 2)) = entry b (cells (i, 3)) + gap ∧
        (2 / 3 : ℝ) * (poolMaximum n : ℝ) ≤ (gap : ℝ) ∧ (gap : ℝ) < poolMaximum n) := by
  let retained := retainedSeedEndpoints candidates 17 (6 * (n + 8)) 2 hcard kept hsub
  have hretained : retained.card = 2 * (6 * (n + 8)) * 16 := by
    dsimp [retained, retainedSeedEndpoints]
    rw [Finset.card_image_of_injective _ hinj, retainedSeedLabels_card, hkept]
  have hlenBridge : ∀ j < 5, (batches j).length = 3 * (n + 8) := by
    intro j hj
    exact (hvalid j hj).1.1
  have hpriorValues : ∀ c ∈ protectedPoolCells a
      (fwBridgeSeedProtectedValues batches candidates hcard kept hsub),
      entry a c ∈ priorBridgeReservation ∅ (Finset.range 5) batches ∪ retained := by
    intro c hc
    exact (mem_protectedPoolCells a _ c).mp hc
  obtain ⟨blocks, hlen, b, hmatched, hpair, hav, hfixed, hroles, hspace, hbounds⟩ :=
    fw_select_and_install_wide_roles bmor upper lower sharp hnlo hnhi m hmlo hmhi
      batches hlenBridge retained hretained hwide hs choice a base
      (protectedPoolCells a (fwBridgeSeedProtectedValues batches candidates hcard kept hsub)) spatial
      hrectbase hprior hpriorValues hdiagfree rows cols hr hc hrows hcols hdisjoint hspatial
  refine ⟨blocks, hlen, b, hmatched, hpair, hav, ?_, hroles, hspace, hbounds⟩
  intro c hv
  exact hfixed c ((mem_protectedPoolCells a _ c).mpr hv)

end
end Sude
