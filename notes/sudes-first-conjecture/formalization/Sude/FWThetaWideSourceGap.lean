import Sude.FWThetaFamilyWitness
import Sude.FWPhysicalDoubleBlockGaps
import Sude.FWPermutedWideGapBounds

/-! Identify the actual destination gap with the stage-permuted source gap
for a supplied theta family. No grid, completion, radius, or prime assertion. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The selected source block determines the physical destination's gap,
including when the two pairs of that block have been swapped. -/
theorem fw_theta_wide_source_gap {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice)
    (j : Fin (3*(n/450))) (b : Fin (3*(n+8))) :
    f.gapw j b = fwPermutedWideSourceGap f.blocks f.hlen f.πw j b := by
  have hsource := fw_wide_physical_selected_double_gap f.hwide f.hs choice f.wr f.wc f.hwr f.hwc
    f.blocks f.hlen _ _ f.hmatched f.source f.hplaced
  have h := hsource.2 j (f.πw j b) (doubleBlockPairSwap (f.sw j b) 0)
  have hdest := f.hinvoicew j b 0
  rw [f.hwideEntry j b 0 true, f.hwideEntry j b 0 false] at hdest
  dsimp only [fwPermutedWideSourceGap] at ⊢
  exact Nat.add_left_cancel (hdest.symm.trans h)

end
end Sude
