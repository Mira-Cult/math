import Sude.FWFourFamilyRoleCoverage
import Sude.FWThetaNetworkWitness
import Sude.FWThetaFamilyWitness
import Sude.LayerPackingSegments
import Sude.ActiveRectangleLineCounts

/-! The physical seed diagonal is exactly the diagonal part of its selected
rectangle support for one supplied family. It does not compare independently
selected witnesses or assert a value bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 100000

/-- For any line contained in the union of the two physical diagonals, the
seed pair image has exactly the selected seed rectangles on that line. -/
theorem fw_seed_reference_diagonal_support {n L : ℕ}
    (choice : Fin L → Bool) (f : FWThetaFamilyWitness n L choice)
    (line : Finset (Cell n)) (hline : line ⊆ mainCells n ∪ antiCells n) :
    (Finset.univ.image (fwSeedExistingPairCells f.hseedrect f.hs choice
      f.sr f.sc f.hsr f.hsc)).filter (fun z => z ∈ line) =
    activeRectangleSupport f.hs choice (Finset.univ.image (fwSeedRectangle f.hseedrect)) ∩ line := by
  classical
  have hr : LayerPacking.PackedLayers (packedRectangleSupport f.hs choice) f.sr :=
    (f.hrows.prefix ((f.br ++ f.sr) ++ f.wr) f.gr).segment f.br f.sr f.wr
  have hc : LayerPacking.PackedLayers
      (LayerPacking.transposeCells (packedRectangleSupport f.hs choice ∪
        LayerPacking.layersSupport (((f.br ++ f.sr) ++ f.wr) ++ f.gr))) f.sc :=
    (f.hcols.prefix ((f.bc ++ f.sc) ++ f.wc) f.gc).segment f.bc f.sc f.wc
  have ho (x : FWSeedOrdinaryInputs n) :
      fwSeedOrdinaryCells f.sr f.sc f.hsr f.hsc x ∉ mainCells n ∧
      fwSeedOrdinaryCells f.sr f.sc f.hsr f.hsc x ∉ antiCells n := by
    cases x with
    | inl x =>
      have hm := LayerPacking.layerSupport_subset (f.sr.get (Fin.cast f.hsr.symm x.1)) f.sr
        (List.get_mem f.sr _) (LayerPacking.sequenceCell_mem f.sr _ x.2)
      exact hr.support_off_diagonals _ hm
    | inr x =>
      have hm : (LayerPacking.sequenceCell f.sc (Fin.cast f.hsc.symm x.1, x.2)).swap ∈
          LayerPacking.transposeCells (LayerPacking.layersSupport f.sc) := by
        exact Finset.mem_image.mpr ⟨_, LayerPacking.layerSupport_subset _ f.sc
          (List.get_mem f.sc _) (LayerPacking.sequenceCell_mem f.sc _ x.2), rfl⟩
      exact (hc.transposed_support_safe _ hm).2
  have hrect :
      Finset.univ.image (fun x : Fin (16 * (4 * 6)) × Fin 4 =>
        packedRectangleCorner f.hs choice (fwSeedRectangle f.hseedrect x.1, x.2)) =
      activeRectangleSupport f.hs choice (Finset.univ.image (fwSeedRectangle f.hseedrect)) := by
    ext z
    simp only [activeRectangleSupport, Finset.mem_image, Finset.mem_product,
      Finset.mem_univ, and_true, true_and]
    constructor
    · rintro ⟨⟨i, j⟩, h⟩
      exact ⟨(fwSeedRectangle f.hseedrect i, j), ⟨i, rfl⟩, h⟩
    · rintro ⟨⟨i, j⟩, ⟨k, rfl⟩, h⟩
      exact ⟨(k, j), h⟩
  have hdis : Disjoint (Finset.univ.image (fwSeedOrdinaryCells f.sr f.sc f.hsr f.hsc)) line := by
    apply Finset.disjoint_left.mpr
    intro z hz hl
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    rcases Finset.mem_union.mp (hline hl) with hm | ha
    · exact (ho x).1 hm
    · exact (ho x).2 ha
  rw [fw_seed_existing_pair_cells_image, hrect]
  simp only [Finset.filter_mem_eq_inter, Finset.union_inter_distrib_right, Finset.disjoint_iff_inter_eq_empty.mp hdis, Finset.union_empty]


end
end Sude
