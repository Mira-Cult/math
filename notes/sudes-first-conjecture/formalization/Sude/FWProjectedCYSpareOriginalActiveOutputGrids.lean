import Sude.FWProjectedCYSpareActiveReference
import Sude.FWCanonicalCYFamilyChoiceGrids
import Sude.FWPermutedRadiusCapacity
import Sude.FWThetaInputs
import Sude.FWPoolBound
import Sude.FlowRealization

/-! Canonical active grids and diagonal keep on the exact supplied-family
projected spare continuation. Targets and the family crossing remain supplied. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 12000000

/-- Preserve the original active-difference continuation and realize its grids
on the same routed square, without selecting another family or completion. -/
theorem fw_projected_cy_spare_original_active_output_grids
    (bmor : BMORFiniteTheta) (lower : RSIndexLower) (upper : RSIndexUpper)
    {n : ℕ} (hnlo : 19485 ≤ n) (hnhi : n ≤ 35733) (hodd : Odd n)
    (otherChoice : Fin (fwJointRectangleCount n 254) → Bool)
    (f : FWThetaFamilyWitness n (fwJointRectangleCount n 254) (fwSelectedThetaChoice hnlo otherChoice))
    (p : Fin 3 → Equiv.Perm (Fin n)) (oldReference : Cell n ≃ Fin (n*n))
    (roles : Finset (Cell n))
    (net : FWThetaNetworkWitness n f.stages.length f.hrect f.hseedrect f.hwide f.hoff f.hs
      (fwSelectedThetaChoice hnlo otherChoice)
      f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
      f.hrows f.hcols p f.ordered oldReference roles)
    (hexp : ∀ S : Finset (Fin n), 519 * min S.card (n - S.card) ≤
      500 * (cutEdges (fun e : Fin 3 × Fin n => e.2) (fun e => p e.1 e.2) S).card)
    (target : Fin n → ℕ) (hprime : ∀ i, Nat.Prime (target i)) (htodd : ∀ i, Odd (target i))
    (htotal : (∑ i, target i) = Lucas.poolTotal n)
    (htarget : ∀ i, |(target i : ℝ) - (n : ℝ) *
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
      (n : ℝ) * centralEntriesMean (prescribedPoolValues n) centralPoolValue / 1240)
    (hcross : (poolMaximum n : ℝ) / 23 ≤ f.last) :
    let choice := fwSelectedThetaChoice hnlo otherChoice
    let labels := fwActiveRectangleLabels n f.stages.length f.stageCap
    let gap := fwOrderedCanonicalRectangleGap f
    let result := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
    let cy := Classical.choose result
    let σ := Classical.choose (Classical.choose_spec result)
    let out := Classical.choose (Classical.choose_spec (Classical.choose_spec result))
    let prior := fw_projected_cy_spare_original_active_difference bmor lower upper hnlo hnhi hodd otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
    fwRetainedProposition prior ∧
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
  let result := fw_projected_cy_spare_transported_target_baseline bmor lower upper hnlo hnhi hodd otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  let cy := Classical.choose result
  let σ := Classical.choose (Classical.choose_spec result)
  let out := Classical.choose (Classical.choose_spec (Classical.choose_spec result))
  have facts := Classical.choose_spec (Classical.choose_spec (Classical.choose_spec result))
  have prior := fw_projected_cy_spare_original_active_difference bmor lower upper hnlo hnhi hodd otherChoice f p oldReference roles net hexp target hprime htodd htotal htarget
  obtain ⟨hcy, hbaseMain, hbaseAnti, htransMain, htransAnti, hoffσ, hroles, hactive, hbalance, hrow, hcol, hfullimage, hunused,
    hr, hc, hmain, hanti, hkeep, hpool, hinj, hoffout, hroleimage, hfullout, hunusedout⟩ := facts
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs (fwSelectedThetaChoice hnlo otherChoice)
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
  have hsub : roles ⊆ fwThetaFamilyFull f := by
    rw [net.roles_eq]
    simpa only [fwThetaFamilyFull] using hgeom.2.2.1
  have hlarge : (4 * 2^30 : ℝ) < poolMaximum n := by
    exact_mod_cast fw_poolMaximum_gt_four_seed lower hnlo
  have hX : (100 : ℝ) ≤ poolMaximum n := by norm_num at hlarge ⊢; linarith
  have hm := fw_actual_pool_mean_bounds_of_theta bmor lower upper hnlo (by omega : n ≤ 35733)
  have hgrids := fw_canonical_cy_family_choice_grids hnlo otherChoice f p oldReference
    roles net cy hcy hcross hX hm.1 hm.2
  have hcorner : ∀ i ∈ fwActiveRectangleLabels n f.stages.length f.stageCap, ∀ k : Fin 4,
      entry out (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k)) =
        entry cy (packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k)) := by
    intro i hi k
    have ha : packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k) ∈
        activeRectangleSupport f.hs (fwSelectedThetaChoice hnlo otherChoice)
          (fwActiveRectangleLabels n f.stages.length f.stageCap) := by
      exact Finset.mem_image.mpr ⟨(i,k), Finset.mem_product.mpr ⟨hi, Finset.mem_univ _⟩, rfl⟩
    have hp : packedRectangleCorner f.hs (fwSelectedThetaChoice hnlo otherChoice) (i,k) ∈
        packedRectangleSupport f.hs (fwSelectedThetaChoice hnlo otherChoice) := by
      exact Finset.mem_image.mpr ⟨(i,k), Finset.mem_univ _, rfl⟩
    rw [hkeep _ hp]
    change entry cy (σ _) = entry cy _
    change ∀ z ∈ activeRectangleSupport f.hs (fwSelectedThetaChoice hnlo otherChoice)
      (fwActiveRectangleLabels n f.stages.length f.stageCap), σ z = z at hactive
    rw [hactive _ ha]
  refine ⟨prior, ?_, ?_, ?_, ?_⟩
  · intro z hz
    apply hoffout z
    intro hzrole
    exact (Finset.mem_sdiff.mp hz).2 (hsub hzrole)
  · intro side
    have hwide := fw_permuted_wide_gap_total_lower
      ((Lucas.poolTotal n : ℝ) / (n*n : ℕ)) hX hm.1 hm.2
      f.blocks f.hlen f.hmatched f.πw (fwCanonicalFamilyDestination side)
    have hcapacity : 2 * ((n / 450) * poolMaximum n) ≤ fwCanonicalFamilyRadius f side := by
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
