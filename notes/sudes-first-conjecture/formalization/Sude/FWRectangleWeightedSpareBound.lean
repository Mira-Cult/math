import Sude.FWRectangleStageOwner
import Sude.FWActiveSpareRectangleMeans

/-! The local active-rectangle stage-mean excess and spare rectangle centered
values share one per-line budget. This does not include the global spare term
inside reservation cancellation, and it does not prove a complete line bound. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1200000

/-- Transfer the actual FW rectangle-owner estimate to physical pair weights.
The supplied stage means must be those used by the subsequent line identity. -/
theorem fw_rectangle_weighted_spare_bound {n P : ℕ} (hP : P ≤ 238)
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
        physicalPairLineWeight cells (fun z => z ∈ active ∩ rowCells r) (j,i) * (stageMean j - μ)) +
        (∑ i ∈ LayerPacking.rowUsed spare r, ((entry a (r,i) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X) ∧
    (∀ c : Fin n,
      |(∑ j : FWFourStageIndex n P, ∑ i : Fin (6*(n+8)),
        physicalPairLineWeight cells (fun z => z ∈ active ∩ columnCells c) (j,i) * (stageMean j - μ)) +
        (∑ i ∈ LayerPacking.colUsed spare c, ((entry a (i,c) : ℝ) - μ))| ≤ (257 / 250 : ℝ) * X) := by
  classical
  letI : Nonempty (FWFourStageIndex n P) := ⟨Sum.inl (Sum.inl (Sum.inl ⟨0, by omega⟩))⟩
  letI : Nonempty (Fin (6 * (n + 8))) := ⟨⟨0, by omega⟩⟩
  dsimp only
  let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
  let active := activeRectangleSupport hs choice (fwActiveRectangleLabels n P hP)
  let spare := packedRectangleSupport hs choice \ active
  have hrectbound := fw_active_spare_rectangle_means_bound hP hs choice
    (physicalPairStageOwner cells) stageMean a X μ hX hstage hvalues hlo hhi
  dsimp only at hrectbound
  have hrset (r : Fin n) : active ∩ rowCells r =
      (LayerPacking.rowUsed active r).image (fun i => (r,i)) := by
    ext ⟨u,v⟩
    simp [rowCells, LayerPacking.rowUsed, and_comm, eq_comm]
    intro h; subst u; rfl
  have hcset (c : Fin n) : active ∩ columnCells c =
      (LayerPacking.colUsed active c).image (fun i => (i,c)) := by
    ext ⟨u,v⟩
    simp [columnCells, LayerPacking.colUsed, and_comm, eq_comm]
    intro h; subst v; rfl
  constructor
  · intro r
    have howner := (fw_rectangle_stage_owner_reindex hP hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
      (rowCells r) (fun j => stageMean j - μ)).2.2
    have hsum : (∑ z ∈ active ∩ rowCells r, (stageMean (physicalPairStageOwner cells z) - μ)) =
        ∑ i ∈ LayerPacking.rowUsed active r, (stageMean (physicalPairStageOwner cells (r,i)) - μ) := by
      rw [hrset, Finset.sum_image]
      intro x hx y hy heq
      exact congrArg Prod.snd heq
    rw [hsum] at howner
    rw [← howner]
    exact (hrectbound.1 r).2
  · intro c
    have howner := (fw_rectangle_stage_owner_reindex hP hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
      (columnCells c) (fun j => stageMean j - μ)).2.2
    have hsum : (∑ z ∈ active ∩ columnCells c, (stageMean (physicalPairStageOwner cells z) - μ)) =
        ∑ i ∈ LayerPacking.colUsed active c, (stageMean (physicalPairStageOwner cells (i,c)) - μ) := by
      rw [hcset, Finset.sum_image]
      intro x hx y hy heq
      exact congrArg Prod.fst heq
    rw [hsum] at howner
    rw [← howner]
    exact (hrectbound.2 c).2

end
end Sude
