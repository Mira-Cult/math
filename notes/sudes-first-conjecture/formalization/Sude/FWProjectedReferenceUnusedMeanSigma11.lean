import Sude.FWReallocatedFullUnusedMeanSigma11
import Sude.FWThetaFamilyDQRFInputs
import Sude.FWThetaNetworkWitness
import Sude.ActiveSupportFullKeepout
import Sude.FWRoleSupportForNetworks

/-! The first-band full-unused-pool mean bound on one supplied projected
family and its same fresh network reference. This does not construct the
projected witness or prove a completion, numerical gate, or prime line. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The ordered family and its supplied reference have the same full
reservation value image and unused pool; both unused means are within
`(11/100) * poolMaximum n` of the prescribed pool mean. -/
theorem fw_projected_reference_unused_mean_sigma11
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
    let μ := centralEntriesMean (prescribedPoolValues n) centralPoolValue
    roles ⊆ full ∧
    full.image (entry oldReference) = full.image (entry f.ordered) ∧
    actualUnusedPool oldReference full = actualUnusedPool f.ordered full ∧
    |centralEntriesMean (actualUnusedPool f.ordered full) centralPoolValue - μ| ≤
      (11 / 100 : ℝ) * (poolMaximum n : ℝ) ∧
    |centralEntriesMean (actualUnusedPool oldReference full) centralPoolValue - μ| ≤
      (11 / 100 : ℝ) * (poolMaximum n : ℝ) := by
  classical
  have hgeom := fw_role_support_for_trace_networks f.stageCap f.hrect f.hseedrect f.hwide f.hoff f.hs choice
    f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc
    f.hrows f.hcols
  dsimp only at hgeom
  have hsub : roles ⊆ fwThetaFamilyFull f := by
    rw [net.roles_eq]
    simpa only [fwThetaFamilyFull] using hgeom.2.2.1
  have hmatched : ∀ block ∈ f.blocks, block.MatchedValid
      (bmorLowBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n)))
      (bmorHighBins (fwReflectedLeft (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))
        (fwReflectedRight (centralEntriesMean (prescribedPoolValues n) centralPoolValue) (poolMaximum n))) := by
    simpa only [prescribedPoolValues_mean] using f.hmatched
  have hbound := fw_reallocated_full_unused_mean_11_100_of_theta bmor lower upper hnlo hnhi f.stageCap
    f.hrect f.hseedrect f.hwide f.hoff f.hs choice f.br f.bc f.sr f.sc f.wr f.wc f.gr f.gc
    f.hbr f.hbc f.hsr f.hsc f.hwr f.hwc f.hgr f.hgc f.hrows f.hcols
    ∅ f.batches f.hvalid f.blocks f.hlen f.source f.ordered f.hdiag f.hord f.hplaced hmatched
    f.πb f.sb f.πw f.sw f.hbridge f.hwideEntry
  have htransport := full_keepout_value_image_and_unused_eq f.ordered oldReference roles
    (fwThetaFamilyFull f) hsub net.off_roles net.roles_image
  dsimp only at hbound ⊢
  have hbound' : |centralEntriesMean (actualUnusedPool f.ordered (fwThetaFamilyFull f)) centralPoolValue -
      centralEntriesMean (prescribedPoolValues n) centralPoolValue| ≤
        (11 / 100 : ℝ) * (poolMaximum n : ℝ) := by
    simpa only [fwThetaFamilyFull] using hbound
  exact ⟨hsub, htransport.1, htransport.2, hbound', by rw [htransport.2]; exact hbound'⟩

end
end Sude
