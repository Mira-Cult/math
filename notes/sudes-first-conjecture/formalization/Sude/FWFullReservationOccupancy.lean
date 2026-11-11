import Sude.FWJointPackedOccupancy

/-! Full-capacity geometric keepout versus the active-label subunion. These
counts do not describe the values in any cells. -/
namespace Sude
noncomputable section

/-- The full joint rectangle capacity contains four distinct corners per label. -/
theorem packed_rectangle_full_card {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) :
    (packedRectangleSupport hs choice).card = 4 * L := by
  classical
  have hu : activeRectangleSupport hs choice Finset.univ = packedRectangleSupport hs choice := by
    simp [activeRectangleSupport, packedRectangleSupport]
  rw [← hu, active_rectangle_support_card]
  simp

/-- Under the normalized joint packings, the full geometric reservation has
exactly the active subunion plus the stated number of spare-capacity corners.
No assertion is made about the values at those cells. -/
theorem fw_full_reservation_occupancy {n P : ℕ} (hP : P ≤ 238)
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
    let active := fwActiveRectangleLayerSupport hP hs choice rows cols
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)
    full \ active = packedRectangleSupport hs choice \ activeRectangleSupport hs choice
      (fwActiveRectangleLabels n P hP) ∧
    (full \ active).card = 96 * (238 - P) ∧
    full.card = 12 * S * (n + 8) + 96 * (238 - P) ∧
    (P < 238 → active.card < full.card) := by
  classical
  dsimp only
  let rows := (((br ++ sr) ++ wr) ++ gr)
  let cols := (((bc ++ sc) ++ wc) ++ gc)
  let rect := packedRectangleSupport hs choice
  let active := fwActiveRectangleLayerSupport hP hs choice rows cols
  let full := rect ∪ LayerPacking.layersSupport rows ∪ LayerPacking.transposeCells (LayerPacking.layersSupport cols)
  have hactive := fw_joint_packed_active_occupancy hP hs choice br sr wr gr bc sc wc gc
    hbr hsr hwr hgr hbc hsc hwc hgc hrows hcols
  dsimp only at hactive
  have hsub : active ⊆ full := hactive.1
  have hrlen : rows.length = 3 * (5 + 16 + 3 * (n / 450) + P) := by
    simp only [rows, List.length_append, hbr, hsr, hwr, hgr]
    omega
  have hclen : cols.length = 3 * (5 + 16 + 3 * (n / 450) + P) := by
    simp only [cols, List.length_append, hbc, hsc, hwc, hgc]
    omega
  have hdis : Disjoint (rect ∪ LayerPacking.layersSupport rows)
      (LayerPacking.transposeCells (LayerPacking.layersSupport cols)) := by
    apply Finset.disjoint_left.mpr
    intro z hz hz'
    exact (hcols.transposed_support_safe z hz').1 hz
  have hccard : (LayerPacking.transposeCells (LayerPacking.layersSupport cols)).card =
      2 * n * cols.length := by
    unfold LayerPacking.transposeCells
    rw [Finset.card_image_of_injective _]
    · exact packed_layers_support_card hcols
    · intro a b hab
      have h := congrArg Prod.swap hab
      simpa using h
  have hfull : full.card = 96 * (254 + 5 + 3 * (n / 450)) +
      12 * n * (5 + 16 + 3 * (n / 450) + P) := by
    dsimp only [full, rect]
    rw [Finset.card_union_of_disjoint hdis, Finset.card_union_of_disjoint hrows.reserved_disjoint,
      packed_rectangle_full_card, packed_layers_support_card hrows, hccard, hrlen, hclen]
    simp only [fwJointRectangleCount]
    ring
  have hactivecard : active.card = 12 * n * (5 + 16 + 3 * (n / 450) + P) +
      96 * (5 + 16 + 3 * (n / 450) + P) := by
    rw [hactive.2.1]
    ring
  have hdifference := Finset.card_sdiff_add_card_eq_card hsub
  constructor
  · change (rect ∪ LayerPacking.layersSupport rows ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport cols)) \ _ = _
    dsimp only [fwActiveRectangleLayerSupport]
    ext z
    simp only [Finset.mem_sdiff, Finset.mem_union]
    have hr : z ∈ rect → z ∉ LayerPacking.layersSupport rows := fun hz hz' =>
      Finset.disjoint_left.mp hrows.reserved_disjoint hz hz'
    have hc : z ∈ rect → z ∉ LayerPacking.transposeCells (LayerPacking.layersSupport cols) := fun hz hz' =>
      Finset.disjoint_left.mp hdis (Finset.mem_union_left _ hz) hz'
    aesop
  constructor
  · change (full \ active).card = 96 * (238 - P)
    rw [hactivecard, hfull] at hdifference
    omega
  constructor
  · rw [hfull]
    have : 12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) =
        12 * n * (5 + 16 + 3 * (n / 450) + P) + 96 * (5 + 16 + 3 * (n / 450) + P) := by ring
    rw [this]
    omega
  · intro hp
    rw [hactivecard, hfull]
    omega

end
end Sude
