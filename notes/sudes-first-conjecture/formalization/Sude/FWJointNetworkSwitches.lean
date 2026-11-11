import Sude.FWJointLayerPacking
import Sude.NetworkSwitches

/-! Simultaneous ordinary network switches for the existing four interleaved
FW packing families. Gap equations and selected subsets are supplied. -/
namespace Sude
noncomputable section
set_option maxRecDepth 4096

/-- Any supplied row/column switch subsets can be performed on the same square
when their actual endpoint gaps and all four family packings are supplied.
All rectangle-reserved cells and both diagonal sums remain fixed. -/
theorem fw_joint_toggle_networks {n : ℕ} (a : Cell n ≃ Fin (n * n))
    (rect : Finset (Cell n)) (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : LayerPacking.PackedLayers rect br)
    (hbc : LayerPacking.PackedLayers (LayerPacking.transposeCells (rect ∪ LayerPacking.layersSupport br)) bc)
    (hsr : LayerPacking.PackedLayers
      ((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) sr)
    (hsc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr)) sc)
    (hwr : LayerPacking.PackedLayers
      ((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) wr)
    (hwc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr)) wc)
    (hgr : LayerPacking.PackedLayers
      ((((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)) gr)
    (hgc : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (((((((rect ∪ LayerPacking.layersSupport br) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport bc)) ∪
        LayerPacking.layersSupport sr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport sc)) ∪
        LayerPacking.layersSupport wr) ∪ LayerPacking.transposeCells (LayerPacking.layersSupport wc)) ∪
        LayerPacking.layersSupport gr)) gc)
    (rowGap : Fin (((br ++ sr) ++ wr) ++ gr).length → Fin n → ℕ)
    (colGap : Fin (((bc ++ sc) ++ wc) ++ gc).length → Fin n → ℕ)
    (hrowGap : ∀ i e, entry a (((((br ++ sr) ++ wr) ++ gr).get i).1 e,
        ((((br ++ sr) ++ wr) ++ gr).get i).2 e) =
      entry a (e, ((((br ++ sr) ++ wr) ++ gr).get i).2 e) + rowGap i e)
    (hcolGap : ∀ i e, entry a (((((bc ++ sc) ++ wc) ++ gc).get i).2 e,
        ((((bc ++ sc) ++ wc) ++ gc).get i).1 e) =
      entry a (((((bc ++ sc) ++ wc) ++ gc).get i).2 e, e) + colGap i e)
    (Sr : Finset (Fin (((br ++ sr) ++ wr) ++ gr).length × Fin n))
    (Sc : Finset (Fin (((bc ++ sc) ++ wc) ++ gc).length × Fin n)) :
    ∃ b : Cell n ≃ Fin (n * n),
      (∀ r, (rowSum b r : ℤ) - (rowSum a r : ℤ) =
        ∑ k ∈ Sr, layerTransfer (((br ++ sr) ++ wr) ++ gr) rowGap k r) ∧
      (∀ c, (columnSum b c : ℤ) - (columnSum a c : ℤ) =
        ∑ k ∈ Sc, layerTransfer (((bc ++ sc) ++ wc) ++ gc) colGap k c) ∧
      mainSum b = mainSum a ∧ antiSum b = antiSum a ∧
      (∀ c ∈ rect, entry b c = entry a c) ∧
      Set.range (entry b) = pool n ∧ Function.Injective (entry b) := by
  obtain ⟨hrows, hcols⟩ := fw_joint_layer_packing rect br bc sr sc wr wc gr gc
    hbr hbc hsr hsc hwr hwc hgr hgc
  exact toggle_two_installed_networks a rect (((br ++ sr) ++ wr) ++ gr) (((bc ++ sc) ++ wc) ++ gc)
    hrows hcols rowGap colGap hrowGap hcolGap Sr Sc

end
end Sude
