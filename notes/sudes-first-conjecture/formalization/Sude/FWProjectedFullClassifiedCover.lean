import Sude.FWProjectedReferenceUnusedMeanSigma11
import Sude.FWWideOutsideQuarter
import Sude.FWWideRoleValueCoverage
import Sude.FWPhysicalDoubleBlockCells
import Sude.FWGroupedBridgeWideGeometry

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1000000

/-- Wide stage reallocations preserve the entire wide value image. -/
private theorem scratch_projected_wide_batch {n L : ℕ} (choice : Fin L → Bool)
    (f : FWThetaFamilyWitness n L choice) :
    (Finset.univ.image (fwWidePhysicalCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc)).image (entry f.ordered) =
      doubleBatchLow f.blocks ∪ doubleBatchHigh f.blocks := by
  classical
  let wide := fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
  have hc : Finset.univ.image wide =
      Finset.univ.image (fwWidePhysicalCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) := by
    change Finset.univ.image (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc ∘
      fwBlockPairIndex (3*(n/450)) n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex (3*(n/450)) n).surjective]
    exact fw_wide_physical_pair_cells_image f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
  have he : Finset.univ.image (fun x => entry f.ordered (wide x)) =
      Finset.univ.image (fun x => entry f.source (wide x)) := by
    ext v
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    constructor
    · rintro ⟨⟨⟨j,k,p⟩,s⟩, hv⟩
      refine ⟨((j, f.πw j k, doubleBlockPairSwap (f.sw j k) p), s), ?_⟩
      exact (f.hwideEntry j k p s).symm.trans hv
    · rintro ⟨⟨⟨j,k,p⟩,s⟩, hv⟩
      let k' := (f.πw j).symm k
      let p' := (doubleBlockPairSwap (f.sw j k')).symm p
      refine ⟨((j,k',p'),s), ?_⟩
      have h := f.hwideEntry j k' p' s
      have hk : f.πw j k' = k := Equiv.apply_symm_apply (f.πw j) k
      have hp : doubleBlockPairSwap (f.sw j k') p' = p := Equiv.apply_symm_apply _ p
      rw [hk, hp] at h
      exact h.trans hv
  have hs := fw_wide_role_values_eq_batch f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
    f.blocks f.hlen f.source f.hplaced
  rw [← hc] at hs ⊢
  simpa only [Finset.image_image, Function.comp_def] using he.trans (by simpa only [Finset.image_image, Function.comp_def] using hs)
end
end Sude

namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 800000

private theorem scratch_fw_narrow_full_card {n P : ℕ}
    (hP : P ≤ 238)
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
      (((bc ++ sc) ++ wc) ++ gc)) :
    let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
      Finset.univ.image (btGrowingOffsetCells
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
    let wideCells := Finset.univ.image (fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc)
    let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
      LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
    (roles \ wideCells).card = 12 * (n + 8) * (5 + 16 + P) ∧
      (full \ wideCells).card = 12 * (n + 8) * (5 + 16 + P) + 96 * (238 - P) ∧
      (full \ wideCells).card ≤ 12 * (n + 8) * 259 := by
  classical
  dsimp only
  let roles := fwGrowthEarlyRoleCells hrect hseed hwide hs choice br bc hbr hbc sr sc hsr hsc wr wc hwr hwc ∪
    Finset.univ.image (btGrowingOffsetCells
      (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc
  let wide := fwWidePhysicalDoubleCells hwide hs choice wr wc hwr hwc
  let wideCells := Finset.univ.image wide
  let full := packedRectangleSupport hs choice ∪ LayerPacking.layersSupport (((br ++ sr) ++ wr) ++ gr) ∪
    LayerPacking.transposeCells (LayerPacking.layersSupport (((bc ++ sc) ++ wc) ++ gc))
  have hfamily := fw_four_family_pair_cells_injective hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have himage : Finset.univ.image cells = roles := hfamily.2
  have hsub : wideCells ⊆ roles := by
    rw [← himage]
    intro z hz
    obtain ⟨x, _, rfl⟩ := Finset.mem_image.mp hz
    apply Finset.mem_image.mpr
    refine ⟨Sum.inl (Sum.inr (fwBlockPairIndex (3 * (n / 450)) n x)), Finset.mem_univ _, ?_⟩
    rfl
  have hgeom := fw_grouped_bridge_wide_geometry hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hwidecard : wideCells.card = 12 * (3 * (n / 450)) * (n + 8) := by
    rw [Finset.card_image_of_injective _ hgeom.2.1, Finset.card_univ]
    simp only [Fintype.card_prod, Fintype.card_fin, Fintype.card_bool]
    ring
  have hrolecard : roles.card = 12 * (5 + 16 + 3 * (n / 450) + P) * (n + 8) :=
    (fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols).2.1
  have hsum : roles.card = 12 * (n+8) * (5+16+P) + 12 * (3 * (n / 450)) * (n+8) := by
    rw [hrolecard]
    ring
  have hc := Finset.card_sdiff_add_card_eq_card hsub
  have hroleRest : (roles \ wideCells).card = 12*(n+8)*(5+16+P) := by omega
  have hocc := fw_role_cell_occupancy hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hfullcard : full.card = 12*(5+16+3*(n/450)+P)*(n+8) + 96*(238-P) := hocc.2.2.2.2.2.2.1
  have hfullsub : wideCells ⊆ full := hsub.trans hocc.1
  have hfullsum : full.card = (12*(n+8)*(5+16+P) + 96*(238-P)) + 12*(3*(n/450))*(n+8) := by
    rw [hfullcard]
    ring
  have hfc := Finset.card_sdiff_add_card_eq_card hfullsub
  have hfullRest : (full \ wideCells).card = 12*(n+8)*(5+16+P) + 96*(238-P) := by omega
  have hspare : 96*(238-P) ≤ 12*(n+8)*(238-P) :=
    Nat.mul_le_mul_right (238-P) (by omega)
  have hcomb : 12*(n+8)*(5+16+P) + 12*(n+8)*(238-P) = 12*(n+8)*259 := by
    rw [← Nat.mul_add]
    congr 1
    omega
  change (roles \ wideCells).card = _ ∧ (full \ wideCells).card = _ ∧ (full \ wideCells).card ≤ _
  exact ⟨hroleRest, hfullRest, by omega⟩

end
end Sude


namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

theorem fw_projected_full_classified_cover
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733)
    (choice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) choice)
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs choice
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles) :
    let full := fwThetaFamilyFull f
    let wide := Finset.univ.image (fwWidePhysicalCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc)
    let accounted := (full \ wide).image (entry f.ordered)
    let shielded := doubleBatchLow f.blocks ∪ doubleBatchHigh f.blocks
    let m : ℝ := (Lucas.poolTotal n : ℝ) / (n*n : ℕ)
    full.image (entry oldReference) ⊆ accounted ∪ shielded ∧
    accounted.card ≤ 12*(n+8)*259 ∧
    (∀ v ∈ shielded, (v : ℝ) ≤ m - (poolMaximum n : ℝ)/4 ∨ m + (poolMaximum n : ℝ)/4 ≤ v) := by
  classical
  dsimp only
  let full := fwThetaFamilyFull f
  let wide := Finset.univ.image (fwWidePhysicalCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc)
  let accounted := (full \ wide).image (entry f.ordered)
  let shielded := doubleBatchLow f.blocks ∪ doubleBatchHigh f.blocks
  let m : ℝ := (Lucas.poolTotal n : ℝ) / (n*n : ℕ)
  have hwide := scratch_projected_wide_batch choice f
  have hgeo := scratch_fw_narrow_full_card f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  dsimp only at hgeo
  have hc : Finset.univ.image (fwWidePhysicalDoubleCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc) = wide := by
    change Finset.univ.image (fwWidePhysicalPairCells f.hwide f.hs choice f.wr f.wc f.hwr f.hwc ∘
      fwBlockPairIndex (3*(n/450)) n) = _
    rw [← Finset.image_image, Finset.image_univ_of_surjective (fwBlockPairIndex (3*(n/450)) n).surjective]
    exact fw_wide_physical_pair_cells_image f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
  have hcard : (full \ wide).card ≤ 12*(n+8)*259 := by
    simpa only [full, fwThetaFamilyFull, hc] using hgeo.2.2
  have htransport := (fw_projected_reference_unused_mean_sigma11 bmor lower upper hnlo hnhi choice f p oldReference roles net).2.1
  have hXnat : 100 ≤ poolMaximum n := by
    have hp := fw_poolMaximum_gt_four_seed lower hnlo
    omega
  have hX : (100:ℝ) ≤ poolMaximum n := by exact_mod_cast hXnat
  have hm := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega)
  have hshield := fw_wide_batch_outside_quarter m (poolMaximum n) hX hm.1 hm.2 f.blocks f.hmatched
  have hcover : full.image (entry oldReference) ⊆ accounted ∪ shielded := by
    rw [htransport]
    intro v hv
    obtain ⟨z,hz,rfl⟩ := Finset.mem_image.mp hv
    by_cases hw : z ∈ wide
    · apply Finset.mem_union_right
      change entry f.ordered z ∈ doubleBatchLow f.blocks ∪ doubleBatchHigh f.blocks
      rw [← hwide]
      exact Finset.mem_image.mpr ⟨z, hw, rfl⟩
    · apply Finset.mem_union_left
      exact Finset.mem_image.mpr ⟨z, Finset.mem_sdiff.mpr ⟨hz, hw⟩, rfl⟩
  refine ⟨hcover, ?_, ?_⟩
  · exact (Finset.card_image_le).trans hcard
  · intro v hv
    rcases Finset.mem_union.mp hv with hv | hv
    · exact Or.inl (hshield.1 v hv)
    · exact Or.inr (hshield.2 v hv)
end
end Sude
