import Sude.FWFourFamilyStageTotals
import Sude.FWRoleSupportForNetworks
import Sude.SpareRectangleLineSeparation
import Sude.RectanglePairInvoice

/-! Pair selected rectangle corners and adjoin them to an active pairing.
This is geometry only; no bound on cell values is claimed. -/
namespace Sude
noncomputable section

/-- Two pairs for each selected rectangle label. -/
abbrev RectangleLabelPairs {L : ℕ} (labels : Finset (Fin L)) :=
  {j : Fin L // j ∈ labels} × Fin 2

/-- Each selected rectangle's four corners are used once. -/
def rectangleLabelPairCells {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (labels : Finset (Fin L)) :
    RectangleLabelPairs labels × Bool → Cell n :=
  fun x => packedRectangleCorner hs choice (x.1.1.val, prefixPairCorner x.1.2 x.2)

theorem rectangle_label_pair_cells_injective {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (labels : Finset (Fin L)) :
    Function.Injective (rectangleLabelPairCells hs choice labels) := by
  rintro ⟨⟨j, p⟩, b⟩ ⟨⟨k, q⟩, c⟩ h
  have he : ((j.val, p), b) = ((k.val, q), c) :=
    (rectanglePairCornerEquiv L).injective ((packedRectangleCorner_injective hs choice) h)
  have hj : j = k := Subtype.ext (congrArg (fun x => x.1.1) he)
  have hp : p = q := congrArg (fun x => x.1.2) he
  have hb : b = c := congrArg Prod.snd he
  cases hj; cases hp; cases hb; rfl

theorem rectangle_label_pair_cells_image {L n : ℕ} (hs : 2 * L + 1 ≤ n)
    (choice : Fin L → Bool) (labels : Finset (Fin L)) :
    Finset.univ.image (rectangleLabelPairCells hs choice labels) =
      activeRectangleSupport hs choice labels := by
  classical
  ext x
  simp only [Finset.mem_image, Finset.mem_univ, true_and, activeRectangleSupport,
    Finset.mem_product]
  constructor
  · rintro ⟨⟨⟨j, p⟩, b⟩, rfl⟩
    exact ⟨(j.val, prefixPairCorner p b), ⟨j.property, True.intro⟩, rfl⟩
  · rintro ⟨⟨j, c⟩, ⟨hj, _⟩, hx⟩
    let y := (rectanglePairCornerEquiv L).symm (j, c)
    have hy : (rectanglePairCornerEquiv L) y = (j, c) := (rectanglePairCornerEquiv L).apply_symm_apply _
    have hyj : y.1.1 = j := congrArg Prod.fst hy
    refine ⟨((⟨y.1.1, hyj ▸ hj⟩, y.1.2), y.2), ?_⟩
    change packedRectangleCorner hs choice ((rectanglePairCornerEquiv L) y) = x
    rw [hy, hx]

/-- Add selected rectangle pairs while retaining active indices and endpoints. -/
def adjoinRectangleLabelPairs {L n : ℕ} {I : Type*}
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (labels : Finset (Fin L))
    (active : I × Bool → Cell n) : (I ⊕ RectangleLabelPairs labels) × Bool → Cell n
  | (Sum.inl i, b) => active (i, b)
  | (Sum.inr j, b) => rectangleLabelPairCells hs choice labels (j, b)

/-- An injective active pairing and precisely its missing rectangle support
form an injective pairing covering the full reservation. -/
theorem adjoin_rectangle_label_pairs_cover {L n : ℕ} {I : Type*} [Fintype I]
    (hs : 2 * L + 1 ≤ n) (choice : Fin L → Bool) (labels : Finset (Fin L))
    (active : I × Bool → Cell n) (full : Finset (Cell n))
    (hinj : Function.Injective active)
    (hsub : Finset.univ.image active ⊆ full)
    (hdiff : full \ Finset.univ.image active = activeRectangleSupport hs choice labels) :
    Function.Injective (adjoinRectangleLabelPairs hs choice labels active) ∧
      Finset.univ.image (adjoinRectangleLabelPairs hs choice labels active) = full := by
  classical
  have hsimg := rectangle_label_pair_cells_image hs choice labels
  have hsdisj : Disjoint (Finset.univ.image active)
      (Finset.univ.image (rectangleLabelPairCells hs choice labels)) := by
    rw [hsimg, ← hdiff]
    exact Finset.disjoint_left.mpr (by
      intro x hx hy
      exact (Finset.mem_sdiff.mp hy).2 hx)
  constructor
  · rintro ⟨i, b⟩ ⟨j, c⟩ h
    cases i with
    | inl i =>
      cases j with
      | inl j =>
        have he := hinj h
        cases he
        rfl
      | inr j =>
        exfalso
        apply Finset.disjoint_left.mp hsdisj
          (Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩)
        exact Finset.mem_image.mpr ⟨(j, c), Finset.mem_univ _, h.symm⟩
    | inr i =>
      cases j with
      | inl j =>
        exfalso
        apply Finset.disjoint_left.mp hsdisj
          (Finset.mem_image.mpr ⟨(j, c), Finset.mem_univ _, rfl⟩)
        exact Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, h⟩
      | inr j =>
        have he := rectangle_label_pair_cells_injective hs choice labels h
        cases he
        rfl
  · ext x
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨i, b⟩, rfl⟩
      cases i with
      | inl i => exact hsub (Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩)
      | inr i =>
        have hm : rectangleLabelPairCells hs choice labels (i, b) ∈
            activeRectangleSupport hs choice labels := by
          rw [← hsimg]
          exact Finset.mem_image.mpr ⟨(i, b), Finset.mem_univ _, rfl⟩
        rw [← hdiff] at hm
        exact (Finset.mem_sdiff.mp hm).1
    · intro hx
      by_cases ha : x ∈ Finset.univ.image active
      · obtain ⟨⟨i, b⟩, _, hi⟩ := Finset.mem_image.mp ha
        exact ⟨(Sum.inl i, b), hi⟩
      · have hm : x ∈ Finset.univ.image (rectangleLabelPairCells hs choice labels) := by
          rw [hsimg, ← hdiff]
          exact Finset.mem_sdiff.mpr ⟨hx, ha⟩
        obtain ⟨⟨i, b⟩, _, hi⟩ := Finset.mem_image.mp hm
        exact ⟨(Sum.inr i, b), hi⟩


/-- The four physical FW families, followed by the unused rectangle pairs,
cover exactly the full reservation on the same packed geometry. -/
theorem fw_full_reservation_pair_cover {n P : ℕ} (hP : P ≤ 238)
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
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) :
    let active := (fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc) ∘ fwFourStageInputEquiv n P
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let combined := adjoinRectangleLabelPairs hs choice (fwSpareRectangleLabels n P hP) active
    Function.Injective combined ∧ Finset.univ.image combined = full := by
  classical
  dsimp only
  have hf := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hr := fw_four_stage_reindex _ hf.1
  have hrole := fw_role_support_for_trace_networks hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hspare := (fw_spare_rectangle_line_separation hP hs choice).2.2.2
  apply adjoin_rectangle_label_pairs_cover hs choice _ _ _ hr.1
  · rw [hr.2, hf.2]
    exact hrole.2.2.1
  · rw [hr.2, hf.2, hrole.2.2.2.1, hspare]

end
end Sude
