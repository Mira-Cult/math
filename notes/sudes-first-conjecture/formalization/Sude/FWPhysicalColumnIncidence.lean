import Sude.FWPhysicalRowIncidence

/-! Column incidence counterpart for the same FW packing, with the generic
arbitrary-line physical pair-count theorem reused from the row module. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

theorem fw_physical_column_incidence {n P : ℕ} (hP : P ≤ 238)
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
      (((bc ++ sc) ++ wc) ++ gc)) (c : Fin n) (value : Cell n → ℝ) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5*(4*6)+16*(4*6)+(3*(n/450))*(4*6)) hoff hs choice gr gc hgr hgc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    let spare := packedRectangleSupport hs choice \ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    ((∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
      physicalPairLineWeight cells (fun z => z.2 = c) (j,i)) +
      ((LayerPacking.colUsed spare c).card : ℝ) = (LayerPacking.colUsed full c).card) ∧
    ((∑ z ∈ columnCells c ∩ (full \ roles), value z) =
      ∑ i ∈ LayerPacking.colUsed spare c, value (i,c)) ∧
    (columnCells c \ full).card = n - (LayerPacking.colUsed full c).card := by
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
  have hpair := injective_pair_line_weight_card cells hi (fun z => z.2 = c)
  rw [him] at hpair
  have hcolset : roles.filter (fun z => z.2 = c) =
      (LayerPacking.colUsed roles c).image (fun i => (i,c)) := by
    ext ⟨u,v⟩
    simp [LayerPacking.colUsed, and_comm, eq_comm]
    intro h; subst v; rfl
  rw [hcolset, Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)] at hpair
  rw [Fintype.sum_prod_type] at hpair
  have hsplit : LayerPacking.colUsed spare c = LayerPacking.colUsed full c \ LayerPacking.colUsed roles c := by
    ext i
    simp [LayerPacking.colUsed, ← hspare]
  have hcolsub : LayerPacking.colUsed roles c ⊆ LayerPacking.colUsed full c := by
    intro i hi'
    simp only [LayerPacking.colUsed, Finset.mem_filter, Finset.mem_univ, true_and] at hi' ⊢
    exact hsub hi'
  have hcard : (LayerPacking.colUsed spare c).card + (LayerPacking.colUsed roles c).card =
      (LayerPacking.colUsed full c).card := by
    rw [hsplit, Finset.card_sdiff_of_subset hcolsub]
    have hh := Finset.card_le_card hcolsub
    omega
  have hcolsp : columnCells c ∩ spare = (LayerPacking.colUsed spare c).image (fun i => (i,c)) := by
    ext ⟨u,v⟩
    simp [columnCells, LayerPacking.colUsed, and_comm, eq_comm]
    intro h; subst v; rfl
  have hcolfull : columnCells c ∩ full = (LayerPacking.colUsed full c).image (fun i => (i,c)) := by
    ext ⟨u,v⟩
    simp [columnCells, LayerPacking.colUsed, and_comm, eq_comm]
    intro h; subst v; rfl
  constructor
  · have hc : ((LayerPacking.colUsed spare c).card : ℝ) + (LayerPacking.colUsed roles c).card =
        (LayerPacking.colUsed full c).card := by exact_mod_cast hcard
    linarith
  constructor
  · rw [hspare, hcolsp, Finset.sum_image]
    intro x hx y hy h
    exact congrArg Prod.fst h
  · have hsubset : columnCells c ∩ full ⊆ columnCells c := Finset.inter_subset_left
    have hdiff : columnCells c \ full = columnCells c \ (columnCells c ∩ full) := by ext x; simp
    rw [hdiff, Finset.card_sdiff_of_subset hsubset, hcolfull,
      Finset.card_image_of_injective _ (fun x y h => congrArg Prod.fst h)]
    rw [columnCells_card_exact]


end
end Sude
