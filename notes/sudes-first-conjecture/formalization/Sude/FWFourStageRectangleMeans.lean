import Sude.FWBridgeWideStageRectangleSplit
import Sude.FWSeedOrdinaryActiveWeight
import Sude.FWGrowthOrdinaryRectanglePhysical
import Sude.FWRectangleWeightedSpareBound

/-! Original-stage physical line incidence and its rectangle/spare mean
correction. Global spare deviation in the reservation cancellation is separate. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

/-- Pointwise stage mass identities give the corresponding weighted sum
identity without any positivity hypothesis. -/
theorem stage_mass_weighted_identity {I J : Type*} [Fintype I] [Fintype J]
    (u v : I → J → ℝ) (f : I → ℝ) (K : ℝ)
    (h : ∀ j, (∑ i, u j i) - (∑ i, v j i) = K) :
    (∑ j, ∑ i, u j i * f j) - K * (∑ j, f j) =
      ∑ j, ∑ i, v j i * f j := by
  simp only [← Finset.sum_mul]
  rw [Finset.mul_sum, ← Finset.sum_sub_distrib]
  apply Finset.sum_congr rfl
  intro j hj
  have hh : (∑ i, u j i) = (∑ i, v j i) + K := by linarith [h j]
  rw [hh]
  ring

/-- All four original stage families have twelve ordinary incidences on each
line, in addition to their actual active rectangle incidences. -/
theorem fw_four_stage_rectangle_line_split {n P : ℕ} (hP : P ≤ 238)
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
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    (∀ j : FWFourStageIndex n P, ∀ r : Fin n,
      (∑ i, physicalPairLineWeight cells (fun z => z.1 = r) (j,i)) -
        (∑ i, physicalPairLineWeight cells (fun z => z ∈ active ∧ z.1 = r) (j,i)) = 12) ∧
    (∀ j : FWFourStageIndex n P, ∀ c : Fin n,
      (∑ i, physicalPairLineWeight cells (fun z => z.2 = c) (j,i)) -
        (∑ i, physicalPairLineWeight cells (fun z => z ∈ active ∧ z.2 = c) (j,i)) = 12) := by
  classical
  dsimp only
  have hb j := fw_bridge_stage_rectangle_line_split hP hrect hs choice br bc sr sc wr wc gr gc hbr hbc hrows hcols j
  have hs' j := fw_seed_ordinary_active_mass hP hseed hs choice br bc sr sc wr wc gr gc hsr hsc hrows hcols j
  have hw j := fw_wide_stage_rectangle_line_split hP hwide hs choice br bc sr sc wr wc gr gc hwr hwc hrows hcols j
  have hg := fw_growth_active_rectangle_ordinary_line_mass hP hoff hs choice
    (((br ++ sr) ++ wr)) (((bc ++ sc) ++ wc)) gr gc hgr hgc hrows hcols
  dsimp only at hb hs' hw hg
  constructor <;> intro j line
  · rcases j with (((j | j) | j) | j)
    · exact hb j |>.1 line
    · exact hs' j |>.1 line
    · exact hw j |>.1 line
    · have he : (fun z : Cell n => z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∧ z.1 = line) =
          (fun z : Cell n => z.1 = line ∧ z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) := by
        funext z; exact propext and_comm
      rw [he]
      change (∑ i, physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
        (fun z => z.1 = line) (j,i)) -
        (∑ i, physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
        (fun z => z.1 = line ∧ z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) (j,i)) = 12
      simpa only [Finset.sum_sub_distrib] using hg.1 j line
  · rcases j with (((j | j) | j) | j)
    · exact hb j |>.2 line
    · exact hs' j |>.2 line
    · exact hw j |>.2 line
    · have he : (fun z : Cell n => z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP) ∧ z.2 = line) =
          (fun z : Cell n => z.2 = line ∧ z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) := by
        funext z; exact propext and_comm
      rw [he]
      change (∑ i, physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
        (fun z => z.2 = line) (j,i)) -
        (∑ i, physicalPairLineWeight (btGrowingOffsetPairCells (Q := 6 * (n + 8)) (by omega) (by omega) (by omega)
        (5 * (4 * 6) + 16 * (4 * 6) + (3 * (n / 450)) * (4 * 6)) hoff hs choice gr gc hgr hgc)
        (fun z => z.2 = line ∧ z ∈ activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)) (j,i)) = 12
      simpa only [Finset.sum_sub_distrib] using hg.2 j line

/-- The physical line-weighted stage means, after subtracting the ordinary
12-per-stage baseline, share the local spare-corner bound. -/
theorem fw_four_stage_weighted_spare_deviation {n P : ℕ} (hP : P ≤ 238)
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
      (((bc ++ sc) ++ wc) ++ gc))
    (a : Cell n ≃ Fin (n*n)) (stageMean : FWFourStageIndex n P → ℝ)
    (X μ : ℝ) (hX : 0 ≤ X)
    (hstage : ∀ j, |stageMean j - μ| ≤ (257 / 500 : ℝ) * X)
    (hvalues : ∀ c : Cell n, 0 ≤ (entry a c : ℝ) ∧ (entry a c : ℝ) ≤ X)
    (hlo : (243 / 500 : ℝ) * X ≤ μ) (hhi : μ ≤ (123 / 250 : ℝ) * X) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
    let spare := packedRectangleSupport hs choice \ active
    (∀ r : Fin n,
      |(∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
        physicalPairLineWeight cells (fun z => z.1 = r) (j,i) * (stageMean j - μ)) -
        12 * (∑ j, (stageMean j - μ)) +
        (∑ i ∈ LayerPacking.rowUsed spare r, ((entry a (r,i) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X) ∧
    (∀ c : Fin n,
      |(∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
        physicalPairLineWeight cells (fun z => z.2 = c) (j,i) * (stageMean j - μ)) -
        12 * (∑ j, (stageMean j - μ)) +
        (∑ i ∈ LayerPacking.colUsed spare c, ((entry a (i,c) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X) := by
  classical
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  let spare := packedRectangleSupport hs choice \ active
  have hmass := fw_four_stage_rectangle_line_split hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
  have hb := fw_rectangle_weighted_spare_bound hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    a stageMean X μ hX hstage hvalues hlo hhi
  dsimp only at hmass hb
  constructor
  · intro r
    have hident := stage_mass_weighted_identity
      (fun j i => physicalPairLineWeight cells (fun z => z.1 = r) (j,i))
      (fun j i => physicalPairLineWeight cells (fun z => z ∈ active ∧ z.1 = r) (j,i))
      (fun j => stageMean j - μ) 12 (fun j => hmass.1 j r)
    have hpred : (fun z : Cell n => z ∈ active ∩ rowCells r) =
        (fun z : Cell n => z ∈ active ∧ z.1 = r) := by
      funext z; simp only [Finset.mem_inter, mem_rowCells]
    have hbrow := hb.1 r
    change |(∑ j, ∑ i, physicalPairLineWeight cells (fun z => z ∈ active ∩ rowCells r) (j,i) * (stageMean j - μ)) +
        (∑ i ∈ LayerPacking.rowUsed spare r, ((entry a (r,i) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X at hbrow
    rw [hpred] at hbrow
    rw [hident]
    exact hbrow
  · intro c
    have hident := stage_mass_weighted_identity
      (fun j i => physicalPairLineWeight cells (fun z => z.2 = c) (j,i))
      (fun j i => physicalPairLineWeight cells (fun z => z ∈ active ∧ z.2 = c) (j,i))
      (fun j => stageMean j - μ) 12 (fun j => hmass.2 j c)
    have hpred : (fun z : Cell n => z ∈ active ∩ columnCells c) =
        (fun z : Cell n => z ∈ active ∧ z.2 = c) := by
      funext z; simp only [Finset.mem_inter, mem_columnCells]
    have hbcol := hb.2 c
    change |(∑ j, ∑ i, physicalPairLineWeight cells (fun z => z ∈ active ∩ columnCells c) (j,i) * (stageMean j - μ)) +
        (∑ i ∈ LayerPacking.colUsed spare c, ((entry a (i,c) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X at hbcol
    rw [hpred] at hbcol
    rw [hident]
    exact hbcol

end
end Sude
