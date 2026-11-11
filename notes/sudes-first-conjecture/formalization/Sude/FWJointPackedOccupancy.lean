import Sude.FWActiveRectangleLayerOccupancy

/-! Occupancy of the active-label geometric subunion of the joint packed
reservation. Spare capacity rectangle cells remain part of the full reservation. -/
namespace Sude
noncomputable section

/-- Full rectangle capacity contains every supplied active rectangle corner. -/
theorem active_rectangle_support_subset_packed {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (active : Finset (Fin L)) :
    activeRectangleSupport hs choice active ⊆ packedRectangleSupport hs choice := by
  intro z hz
  obtain ⟨i, _, hi⟩ := Finset.mem_image.mp hz
  exact Finset.mem_image.mpr ⟨i, Finset.mem_univ _, hi⟩

/-- The joint packed interface supplied by the theta construction implies the
occupancy conclusions for the active-label subunion. The full rectangle
reservation also includes all spare-capacity labels. -/
theorem fw_joint_packed_active_occupancy {n P : ℕ} (hP : P ≤ 238)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br sr wr gr bc sc wc gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hsr : sr.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hgr : gr.length = P * 3)
    (hbc : bc.length = 5 * 3) (hsc : sc.length = 16 * 3)
    (hwc : wc.length = (3 * (n / 450)) * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice)
      (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) :
    let S := 5 + 16 + 3 * (n / 450) + P
    let rows := (((br ++ sr) ++ wr) ++ gr)
    let cols := (((bc ++ sc) ++ wc) ++ gc)
    let total := fwActiveRectangleLayerSupport hP hs choice rows cols
    total ⊆ packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols) ∧
    total.card = 12 * S * (n + 8) ∧
    (∀ r, (LayerPacking.rowUsed total r).card = 12 * S ∨
      (LayerPacking.rowUsed total r).card = 12 * S + 2) ∧
    (∀ c, (LayerPacking.colUsed total c).card = 12 * S ∨
      (LayerPacking.colUsed total c).card = 12 * S + 2) := by
  classical
  dsimp only
  let rows := (((br ++ sr) ++ wr) ++ gr)
  let cols := (((bc ++ sc) ++ wc) ++ gc)
  have hsub := active_rectangle_support_subset_packed hs choice (fwActiveRectangleLabels n P hP)
  have hrdis : Disjoint (activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP))
      (LayerPacking.layersSupport rows) := hrows.reserved_disjoint.mono_left hsub
  have hsafe := hcols.transposed_support_safe
  have hcdis : Disjoint (activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP))
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (hsafe z hz').1 (Finset.mem_union_left _ (hsub hz))
  have hrcdis : Disjoint (LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (hsafe z hz').1 (Finset.mem_union_right _ hz)
  have hrlen : rows.length = 3 * (5 + 16 + 3 * (n / 450) + P) := by
    simp only [rows, List.length_append, hbr, hsr, hwr, hgr]
    omega
  have hclen : cols.length = 3 * (5 + 16 + 3 * (n / 450) + P) := by
    simp only [cols, List.length_append, hbc, hsc, hwc, hgc]
    omega
  have h := fw_active_rectangle_layer_occupancy hP hs choice rows cols
    (packedRectangleSupport hs choice)
    (LayerPacking.transposeCells (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows))
    hrows hcols hrlen hclen hrdis hcdis hrcdis
  dsimp only at h
  constructor
  · intro z hz
    dsimp [fwActiveRectangleLayerSupport] at hz
    rcases Finset.mem_union.mp hz with hz | hz
    · rcases Finset.mem_union.mp hz with hz | hz
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ (hsub hz))
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ hz)
    · exact Finset.mem_union_right _ hz
  · exact ⟨h.1, h.2.2.2.1, h.2.2.2.2⟩

end
end Sude
