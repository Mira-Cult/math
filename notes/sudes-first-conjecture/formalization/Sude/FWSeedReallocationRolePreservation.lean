import Sude.FWSeedBridgeRolePreservation
import Sude.FWSeedReallocationWidePreservation
import Sude.FWSeedReallocationGrowthPreservation

/-! The actual packed bridge, wide and growth roles survive seed-only
reallocation. This does not preserve seed diagonal sums or any old invoice. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096
set_option maxHeartbeats 800000

/-- The original geometric packing hypotheses discharge both rectangle-avoidance
conditions, so seed-only changes preserve the entries of all other roles. -/
theorem fw_seed_reallocation_preserves_other_roles {n L P : ℕ}
    (hrect : 5 * (4 * 6) ≤ L) (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ L)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ L)
    (hgrowth : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ L)
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool)
    (rows cols : List (LayerPacking.Layer n)) (hr : rows.length = 5 * 3) (hc : cols.length = 5 * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) rows)
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows)) cols)
    (sr sc : List (LayerPacking.Layer n)) (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hsrows : LayerPacking.PackedLayers
      ((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) sr)
    (hscols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr)) sc)
    (hsdisj : Disjoint (LayerPacking.layersSupport sr) (LayerPacking.transposeCells (LayerPacking.layersSupport sc)))
    (wr wc : List (LayerPacking.Layer n)) (hwr : wr.length = (3 * (n / 450)) * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3)
    (hwrows : LayerPacking.PackedLayers
      ((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport cols)) ∪ LayerPacking.layersSupport sr) ∪
        LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪ LayerPacking.layersSupport wr)) wc)
    (gr gc : List (LayerPacking.Layer n)) (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hgrpacked : LayerPacking.PackedLayers (fwGrowthEarlyBase hs choice rows cols sr sc wr wc) gr)
    (hgcpacked : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (fwGrowthEarlyBase hs choice rows cols sr sc wr wc ∪ LayerPacking.layersSupport gr)) gc)
    (hgdisj : Disjoint (LayerPacking.layersSupport gr) (LayerPacking.transposeCells (LayerPacking.layersSupport gc)))
    (grown b : Cell n ≃ Fin (n*n))
    (hfixed : ∀ c, c ∉ Set.range (fwSeedExistingPairCells hseed hs choice sr sc hsr hsc) →
      entry b c = entry grown c) :
    (∀ t side, entry b (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side)) =
      entry grown (packedRectangleCorner hs choice (bridgeDiagonalRectangle hrect t, side))) ∧
    (∀ x, entry b (fwBridgeLayerCells rows cols hr hc x) =
      entry grown (fwBridgeLayerCells rows cols hr hc x)) ∧
    (∀ x : FWWideInputs n, entry b (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x) =
      entry grown (fwWidePhysicalCells hwide hs choice wr wc hwr hwc x)) ∧
    (∀ x : PrefixPhysicalInputs P 6 3 n,
      entry b (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hgrowth hs choice gr gc hgr hgc x) =
      entry grown (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hgrowth hs choice gr gc hgr hgc x)) := by
  have hwdisj : Disjoint (LayerPacking.layersSupport wr) (LayerPacking.transposeCells (LayerPacking.layersSupport wc)) := by
    apply Finset.disjoint_left.mpr
    intro c hc' hd'
    exact (hwcols.transposed_support_safe c hd').1 (Finset.mem_union_right _ hc')
  have hwidefree := fw_wide_corner_avoids_bridge_seed_roles hrect hseed hwide hs choice
    rows cols hr hc hrows hcols sr sc hsr hsc hsrows hscols hsdisj
  have hgrowthfree := fw_growth_corner_avoids_early_roles hrect hseed hwide hgrowth hs choice
    rows cols hr hc hrows hcols sr sc hsr hsc hsrows hscols hsdisj wr wc hwr hwc hwrows hwcols
  obtain ⟨hbridgeRect, hbridgeOrd⟩ := fw_seed_reallocation_preserves_bridge_roles
    hrect hseed hs choice rows cols sr sc hr hc hsr hsc hrows hcols hsrows hscols grown b hfixed
  exact ⟨hbridgeRect, hbridgeOrd,
    fw_seed_reallocation_preserves_wide_roles hrect hseed hwide hs choice rows cols hr hc
      sr sc hsr hsc wr wc hwr hwc hwrows hwcols hwdisj hwidefree grown b hfixed,
    fw_seed_reallocation_preserves_growth_roles hrect hseed hwide hgrowth hs choice rows cols hr hc
      sr sc hsr hsc wr wc hwr hwc gr gc hgr hgc hgrpacked hgcpacked hgdisj hgrowthfree grown b hfixed⟩

end
end Sude
