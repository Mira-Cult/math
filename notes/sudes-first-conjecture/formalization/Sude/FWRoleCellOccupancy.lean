import Sude.FWRoleSupportEquality
import Sude.FWFullReservationOccupancy

/-! The actual role-cell image has the active geometric occupancy, while the
full rectangle-capacity reservation includes spare corners. This is geometry
only and asserts nothing about the values of those cells. -/
namespace Sude
noncomputable section

/-- Role occupancy and its gap from the full geometric reservation, under the
normalized joint packing interface and the explicit stage index bounds. -/
theorem fw_role_cell_occupancy {n P : ℕ} (hP : P ≤ 238)
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
    let S := 5 + 16 + 3 * (n / 450) + P
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    roles ⊆ full ∧
    roles.card = 12 * S * (n + 8) ∧
    (∀ r, (LayerPacking.rowUsed roles r).card = 12 * S ∨
      (LayerPacking.rowUsed roles r).card = 12 * S + 2) ∧
    (∀ c, (LayerPacking.colUsed roles c).card = 12 * S ∨
      (LayerPacking.colUsed roles c).card = 12 * S + 2) ∧
    full \ roles = packedRectangleSupport hs choice \ activeRectangleSupport hs choice
      (fwActiveRectangleLabels n P hP) ∧
    (full \ roles).card = 96 * (238 - P) ∧
    full.card = 12 * S * (n + 8) + 96 * (238 - P) ∧
    (P < 238 → roles.card < full.card) := by
  classical
  dsimp only
  rw [fw_role_cells_eq_active_support hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc]
  have hroles := fw_joint_packed_active_occupancy hP hs choice br sr wr gr bc sc wc gc
    hbr hsr hwr hgr hbc hsc hwc hgc hrows hcols
  have hfull := fw_full_reservation_occupancy hP hs choice br sr wr gr bc sc wc gc
    hbr hsr hwr hgr hbc hsc hwc hgc hrows hcols
  exact ⟨hroles.1, hroles.2.1, hroles.2.2.1, hroles.2.2.2,
    hfull.1, hfull.2.1, hfull.2.2.1, hfull.2.2.2⟩

end
end Sude
