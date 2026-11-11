import Sude.FWFourStageRectangleMeans
import Sude.FWFourFamilyStageMeanSumOfTheta

/-! Same-square four-stage rectangle/spare mean correction, conditional on
finite-theta and RS index inputs. No full-line or later-flow claim. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 1600000

theorem fw_four_stage_weighted_spare_deviation_of_theta
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n P : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hP : P ≤ 238)
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
    (a : Cell n ≃ Fin (n*n)) :
    let cells := fwFourFamilyPairCells hrect hseed hwide hoff hs choice
      br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc ∘ fwFourStageInputEquiv n P
    let stageMean := fun j : FWFourStageIndex n P =>
      (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) /
        ((6 * (n + 8) : ℕ) : ℝ)
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    let X : ℝ := poolMaximum n
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
  let stageMean := fun j : FWFourStageIndex n P =>
    (∑ i, (((entry a (cells ((j,i),false)) : ℝ) + entry a (cells ((j,i),true))) / 2)) /
      ((6 * (n + 8) : ℕ) : ℝ)
  let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
  have hmean : ∀ j, |stageMean j - μ| ≤ (257 / 500 : ℝ) * (poolMaximum n : ℝ) :=
    fw_four_stage_mean_coarse_of_theta bmor lower upper hnlo hnhi (by omega) a cells
  obtain ⟨hlo, hhi⟩ := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo hnhi
  rw [← prescribedPoolValues_mean] at hlo hhi
  exact fw_four_stage_weighted_spare_deviation hP hrect hseed hwide hoff hs choice
    br bc sr sc wr wc gr gc hbr hbc hsr hsc hwr hwc hgr hgc hrows hcols
    a stageMean (poolMaximum n : ℝ) μ (by positivity) hmean (physical_entry_pool_range a) hlo hhi

end
end Sude
