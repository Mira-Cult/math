import Sude.FWRoleCellOccupancy

/-! Active-role and full-reservation geometry for the trace networks. This
constructs no witness and gives no bound on the values of spare cells. -/
namespace Sude
noncomputable section
set_option maxRecDepth 16384

/-- With the same complete rectangle choice and growth offset, the actual
role set contains both network supports. The full reservation also includes
exactly the unused rectangle corners, whose number is explicit. -/
theorem fw_role_support_for_trace_networks {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ⊆ roles ∧
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc)) ⊆ roles ∧
    roles ⊆ full ∧
    full \ roles = packedRectangleSupport hs choice \ activeRectangleSupport hs choice
      (fwActiveRectangleLabels n P hP) ∧
    (full \ roles).card = 96 * (238 - P) := by
  classical
  dsimp only
  have hrole := fw_role_cells_eq_active_support hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  refine ⟨?_, ?_, hocc.1, hocc.2.2.2.2.1, hocc.2.2.2.2.2.1⟩
  · rw [hrole]
    intro c hc
    exact Finset.mem_union_left _ (Finset.mem_union_right _ hc)
  · rw [hrole]
    intro c hc
    exact Finset.mem_union_right _ hc

end
end Sude
