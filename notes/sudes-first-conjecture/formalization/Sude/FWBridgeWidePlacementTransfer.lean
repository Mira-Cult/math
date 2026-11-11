import Sude.FWGrowthEarlyGeometry
import Sude.FWBridgeWidePairPlacement

/-! Same-choice transfer of supplied bridge and wide placements through
the early-role-preserving growth and seed reallocation steps. -/

namespace Sude
noncomputable section

/-- Transfer the actual bridge and wide placement equations along a supplied
old → grown → seed-reallocated square chain. All three squares use the same
choice and the same physical role cells. -/
theorem fw_bridge_wide_placement_transfer {n L : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (br bc sr sc wr wc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (initial : Finset ℕ) (batches : ℕ → List DoublePair)
    (hvalid : ∀ j < 5, FWBridgeSequentialValid n initial batches j)
    (blocks : List DoublePair) (hlen : blocks.length = (3 * (n / 450)) * (3 * (n + 8)))
    (old grown b : Cell n ≃ Fin (n * n))
    (hfixed : ∀ c ∈ fwGrowthEarlyRoleCells hrect hseed hwide hs choice
      br bc hbr hbc sr sc hsr hsc wr wc hwr hwc, entry grown c = entry old c)
    (hbdPres : ∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      entry grown (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)))
    (hboPres : ∀ x, entry b (fwBridgeLayerCells br bc hbr hbc x) =
      entry grown (fwBridgeLayerCells br bc hbr hbc x))
    (hwPres : ∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x))
    (hbd : ∀ t side, entry old (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side)))
    (hbo : ∀ x, entry old (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x))
    (hw : ∀ x : FWWideInputs n, entry old (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) :
    (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeDiagonalSlot n (t, side))) ∧
    (∀ x, entry b (fwBridgeLayerCells br bc hbr hbc x) =
      fwBridgeStageEndpoint n initial batches hvalid (fwBridgeOrdinarySlot n x)) ∧
    (∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      doublePairSequenceEndpoint blocks (Fin.cast hlen.symm (fwWideFlatSlot n x).1, (fwWideFlatSlot n x).2)) := by
  classical
  constructor
  · intro t side
    rw [hbdPres]
    rw [hfixed _ (by
      simp only [fwGrowthEarlyRoleCells, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inl ⟨(t,side), rfl⟩)))]
    exact hbd t side
  constructor
  · intro x
    rw [hboPres]
    rw [hfixed _ (by
      simp only [fwGrowthEarlyRoleCells, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inl (Or.inl (Or.inr ⟨x, rfl⟩)))]
    exact hbo x
  · intro x
    rw [hwPres]
    rw [hfixed _ (by
      simp only [fwGrowthEarlyRoleCells, Finset.mem_union, Finset.mem_image, Finset.mem_univ, true_and]
      exact Or.inr ⟨x, rfl⟩)]
    exact hw x

end
end Sude
