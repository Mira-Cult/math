import Sude.FWFourFamilyStageTotals
import Sude.FWRoleSupportForNetworks
import Sude.PhysicalPairLineSum
import Sude.DiagonalLineTransfer

/-! Physical row incidence on the actual FW four-family image and full
reservation. These are exact finite-set identities, not value bounds. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Each selected physical endpoint contributes one to the total pair weight. -/
theorem injective_pair_line_weight_card {α : Type*} [Fintype α] {n : ℕ}
    (cells : α × Bool → Cell n) (hinj : Function.Injective cells)
    (line : Cell n → Prop) [DecidablePred line] :
    (∑ p, physicalPairLineWeight cells line p) =
      (((Finset.univ.image cells).filter line).card : ℝ) := by
  classical
  calc
    _ = ∑ x : α × Bool, if line (cells x) then (1 : ℝ) else 0 := by
      rw [Fintype.sum_prod_type]
      apply Finset.sum_congr rfl
      intro p hp
      rw [Fintype.sum_bool]
      unfold physicalPairLineWeight
      split_ifs <;> ring
    _ = ∑ z ∈ (Finset.univ.image cells).filter line, (1 : ℝ) := by
      rw [Finset.sum_filter, Finset.sum_image (by intro x _ y _ h; exact hinj h)]
    _ = _ := by simp

/-- Exact row incidence and geometric spare/free-cell conversions for the
same supplied FW packing. -/
theorem fw_physical_row_incidence {n P : ℕ} (hP : P ≤ 238)
    (hrect : 5 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hseed : 5 * (4 * 6) + 16 * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hwide : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hoff : 5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6) + P * (4 * 6) ≤ fwJointRectangleCount n 254)
    (hs : 2 * fwJointRectangleCount n 254 + 1 ≤ n) (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (br bc sr sc wr wc gr gc : List (LayerPacking.Layer n))
    (hbr : br.length = 5 * 3) (hbc : bc.length = 5 * 3)
    (hsr : sr.length = 16 * 3) (hsc : sc.length = 16 * 3)
    (hwr : wr.length = (3 * (n / 450)) * 3) (hwc : wc.length = (3 * (n / 450)) * 3)
    (hgr : gr.length = P * 3) (hgc : gc.length = P * 3)
    (hrows : LayerPacking.PackedLayers (packedRectangleSupport hs choice) (((br ++ sr) ++ wr) ++ gr))
    (hcols : LayerPacking.PackedLayers (LayerPacking.transposeCells
      (packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr)))
      (((bc ++ sc) ++ wc) ++ gc)) (r : Fin n) (value : Cell n → ℝ) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    ((∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
      physicalPairLineWeight cells (fun z => z.1 = r) (j,i)) +
      ((LayerPacking.rowUsed spare r).card : ℝ) = (LayerPacking.rowUsed full r).card) ∧
    ((∑ z ∈ rowCells r ∩ (full \ roles), value z) =
      ∑ i ∈ LayerPacking.rowUsed spare r, value (r,i)) ∧
    (rowCells r \ full).card = n - (LayerPacking.rowUsed full r).card := by
  classical
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  have hp := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hp
  have hi : Function.Injective cells := hp.1.comp (fwFourStageInputEquiv n P).injective
  have him : Finset.univ.image cells = roles := by
    simpa only [cells, ← Finset.image_image, Finset.image_univ_of_surjective
      (fwFourStageInputEquiv n P).surjective] using hp.2
  have hg := fw_role_support_for_trace_networks hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  dsimp only at hg
  have hsub : roles ⊆ full := hg.2.2.1
  have hspare : full \ roles = spare := hg.2.2.2.1
  have hpair := injective_pair_line_weight_card cells hi (fun z => z.1 = r)
  rw [him] at hpair
  have hrowset : roles.filter (fun z => z.1 = r) =
      (LayerPacking.rowUsed roles r).image (fun i => (r,i)) := by
    ext ⟨u,v⟩
    simp [LayerPacking.rowUsed, and_comm, eq_comm]
    intro h; subst u; rfl
  rw [hrowset, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.snd h)] at hpair
  rw [Fintype.sum_prod_type] at hpair
  have hsplit : LayerPacking.rowUsed spare r = LayerPacking.rowUsed full r \ LayerPacking.rowUsed roles r := by
    ext i
    simp [LayerPacking.rowUsed, ← hspare]
  have hrowsub : LayerPacking.rowUsed roles r ⊆ LayerPacking.rowUsed full r := by
    intro i hi'
    simp only [LayerPacking.rowUsed, Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
    exact hsub hi'
  have hcard : (LayerPacking.rowUsed spare r).card + (LayerPacking.rowUsed roles r).card =
      (LayerPacking.rowUsed full r).card := by
    rw [hsplit, Finset.card_sdiff_of_subset hrowsub]
    have hh := Finset.card_le_card hrowsub
    omega
  have hrowsp : rowCells r ∩ spare = (LayerPacking.rowUsed spare r).image (fun i => (r,i)) := by
    ext ⟨u,v⟩
    simp [rowCells, LayerPacking.rowUsed, and_comm, eq_comm]
    intro h; subst u; rfl
  have hrowfull : rowCells r ∩ full = (LayerPacking.rowUsed full r).image (fun i => (r,i)) := by
    ext ⟨u,v⟩
    simp [rowCells, LayerPacking.rowUsed, and_comm, eq_comm]
    intro h; subst u; rfl
  constructor
  · have hc : ((LayerPacking.rowUsed spare r).card : ℝ) + (LayerPacking.rowUsed roles r).card =
        (LayerPacking.rowUsed full r).card := by exact_mod_cast hcard
    linarith
  constructor
  · rw [hspare, hrowsp, Finset.sum_image]
    intro x hx y hy h
    exact congrArg Prod.snd h
  · have hsubset : rowCells r ∩ full ⊆ rowCells r := Finset.inter_subset_left
    have hdiff : rowCells r \ full = rowCells r \ (rowCells r ∩ full) := by ext x; simp
    rw [hdiff, Finset.card_sdiff_of_subset hsubset, hrowfull,
      Finset.card_image_of_injective _ (fun x y h => congrArg Prod.snd h)]
    rw [rowCells_card_exact]

end
end Sude
