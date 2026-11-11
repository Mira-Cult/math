import Sude.FWSelectedCapacityCYSpareTargetRouting
import Sude.FWSelectedCapacityCYFamilyGrids
import Sude.FWRoleSupportForNetworks

/-! Grid and keep facts for the exact supplied-target routing witnesses. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- The routed output realizes both canonical grids on active rectangles and
agrees with the rebalanced completion on unreserved diagonals. -/
theorem fw_selected_capacity_cy_spare_output_grids
    (mv : MVBrunTitchmarsh) (bmor : BMORFiniteTheta)
    (upper : RSIndexUpper) (lower : RSIndexLower)
    (sharp : RSIndexLowerSharp) (upperSharp : RSIndexUpperSharp)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 21248) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (a : Cell n ≃ Fin (n*n)) (seeds : Finset ℕ)
    (hseed : ∀ p ∈ seeds, p + 2 ≤ 2 ^ 30)
    (hseedPrime : ∀ p ∈ seeds, 43 < p ∧ Nat.Prime p ∧ Nat.Prime (p + 2))
    (hseedCount : 6 * (n + 8) * (16 + 2 - 1) ≤ seeds.card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240) :
    let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
    let f := w.family
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
    let gap := fwOrderedCanonicalRectangleGap f
    let result := fw_selected_capacity_cy_spare_nominal_target_routing mv bmor upper lower sharp upperSharp hnlo hnhi hodd otherChoice a seeds hseed hseedPrime hseedCount target hprime htodd htotal htarget
    let cy := Classical.choose result
    let σ := Classical.choose (Classical.choose_spec result)
    let out := Classical.choose (Classical.choose_spec (Classical.choose_spec result))
    let facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec result))
    fwRetainedProposition facts ∧
    (∀ z ∈ unreservedDiagonalCells (fwThetaFamilyFull f), entry out z = entry (σ.trans cy) z) ∧
    (∀ side, CompleteEvenGrid (labels.filter fun i => choice i = side) gap (fwCanonicalFamilyRadius f side) ∧
      2 ∣ fwCanonicalFamilyRadius f side ∧
      2 * ((n / 450) * poolMaximum n) ≤ fwCanonicalFamilyRadius f side ∧
      2 * (((n / 450) * poolMaximum n) / 2) ≤ evenGridCenter (fwCanonicalFamilyRadius f side)) ∧
    (∀ i ∈ labels, ∀ k : Fin 4,
      entry out (packedRectangleCorner f.hs choice (i,k)) =
        entry f.ordered (packedRectangleCorner f.hs choice (i,k))) ∧
    (∀ i ∈ labels,
      entry out (packedRectangleCorner f.hs choice (i,1)) =
        entry out (packedRectangleCorner f.hs choice (i,0)) + gap i ∧
      entry out (packedRectangleCorner f.hs choice (i,2)) =
        entry out (packedRectangleCorner f.hs choice (i,3)) + gap i) := by
  classical
  dsimp only
  let w := fwSelectedCapacityThetaWitness mv bmor upper lower sharp upperSharp n hnlo hnhi otherChoice a seeds hseed hseedPrime hseedCount
  let result := fw_selected_capacity_cy_spare_nominal_target_routing mv bmor upper lower sharp upperSharp hnlo hnhi hodd otherChoice a seeds hseed hseedPrime hseedCount target hprime htodd htotal htarget
  let cy := Classical.choose result
  let σ := Classical.choose (Classical.choose_spec result)
  let out := Classical.choose (Classical.choose_spec (Classical.choose_spec result))
  have facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec result))
  have factsOriginal := facts
  obtain ⟨hcy, hoffσ, hroles, hactive, hbalance, hrow, hcol, hfullimage, hunused,
    hr, hc, hmain, hanti, hkeep, hpool, hinj, hoffout, hroleimage, hfullout, hunusedout⟩ := facts
  have hgeom := fw_role_support_for_trace_networks w.family.stageCap w.family.hrect w.family.hseedrect w.family.hwide w.family.hoff w.family.hs (fwSelectedThetaChoice hnlo otherChoice)
    w.family.br w.family.bc w.family.sr w.family.sc w.family.wr w.family.wc w.family.gr w.family.gc w.family.hbr w.family.hbc w.family.hsr w.family.hsc w.family.hwr w.family.hwc w.family.hgr w.family.hgc w.family.hrows w.family.hcols
  have hsub : w.roles ⊆ fwThetaFamilyFull w.family := by
    rw [w.network.roles_eq]
    simpa only [fwThetaFamilyFull] using hgeom.2.2.1
  have hlarge : (4 * 2^30 : ℝ) < poolMaximum n := by
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  have hX : (100 : ℝ) ≤ poolMaximum n := by norm_num at hlarge ⊢; linarith
  have hm := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega : n ≤ 35733)
  have hgrids := fw_canonical_cy_family_choice_grids hnlo otherChoice w.family w.p w.oldReference
    w.roles w.network cy hcy w.cross hX hm.1 hm.2
  have hcorner : ∀ i ∈ fwActiveRectangleLabels n w.family.stages.length w.family.stageCap, ∀ k : Fin 4,
      entry out (packedRectangleCorner w.family.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k)) =
        entry cy (packedRectangleCorner w.family.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k)) := by
    intro i hi k
    have ha : packedRectangleCorner w.family.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k) ∈
        activeRectangleSupport w.family.hs (fwSelectedThetaChoice hnlo otherChoice)
          (fwActiveRectangleLabels n w.family.stages.length w.family.stageCap) := by
      exact Finset.mem_image.mpr ⟨(i,k), Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, rfl⟩
    have hp : packedRectangleCorner w.family.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k) ∈
        packedRectangleSupport w.family.hs (fwSelectedThetaChoice hnlo otherChoice) := by
      exact Finset.mem_image.mpr ⟨(i,k), Finset.mem_univ _, rfl⟩
    rw [hkeep _ hp]
    change entry cy (σ _) = entry cy _
    change ∀ z ∈ activeRectangleSupport w.family.hs (fwSelectedThetaChoice hnlo otherChoice)
      (fwActiveRectangleLabels n w.family.stages.length w.family.stageCap), σ z = z at hactive
    rw [hactive _ ha]
  refine ⟨factsOriginal, ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply hoffout z
    intro hzrole
    exact (Finset.mem_sdiff.mp hz).2 (hsub hzrole)
  · intro side
    have hwide := fw_permuted_wide_gap_total_lower
      ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) hX hm.1 hm.2
      w.family.blocks w.family.hlen w.family.hmatched w.family.πw (fwCanonicalFamilyDestination side)
    have hcapacity : 2 * ((n / 450) * poolMaximum n) ≤ fwCanonicalFamilyRadius w.family side := by
      dsimp [fwCanonicalFamilyRadius]
      omega
    exact ⟨(hgrids.1 side).1, (hgrids.1 side).2, hcapacity,
      evenGridCenter_pays_capacity _ _ hcapacity⟩
  · intro i hi k
    rw [hcorner i hi k]
    apply hgrids.2.1
    exact Finset.mem_image.mpr ⟨(i,k), Finset.mem_univ _, rfl⟩
  · intro i hi
    rw [hcorner i hi 1, hcorner i hi 0, hcorner i hi 2, hcorner i hi 3]
    exact hgrids.2.2.1 i hi

end
end Sude
