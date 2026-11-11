import Sude.FWThetaFamilyWitness
import Sude.FWPhysicalDoubleBlockGaps
import Sude.FWStageVaryingBridgeGrid

/-! The actual ordered bridge gap is the stage-permuted source block gap.
No grid, CY, radius or primality claim is made. -/
namespace Sude
noncomputable section
set_option maxRecDepth 32768
set_option maxHeartbeats 4000000

/-- The source pair swap is accounted for before comparing the two oriented
physical equations on the same family witness. -/
theorem fw_theta_bridge_source_gap {n L : ℕ} {choice : Fin L → Bool}
    (f : FWThetaFamilyWitness n L choice) (j : Fin 5) (k : Fin (3*(n+8))) :
    f.gapb j k = selectedBridgeGap f.batches (f.πb j k) j := by
  have hsource := fw_bridge_physical_double_common_gap f.hrect f.hs choice f.br f.bc f.hbr f.hbc
    ∅ f.batches f.hvalid f.source f.hdiag f.hord j (f.πb j k)
      (doubleBlockPairSwap (f.sb j k) 0)
  dsimp only at hsource
  have hordered := f.hinvoiceb j k 0
  rw [f.hbridge j k 0 true, f.hbridge j k 0 false] at hordered
  have heq := Nat.add_left_cancel (hordered.symm.trans hsource)
  rw [← fwBridgeStageBlock_gap n ∅ f.batches f.hvalid j (f.πb j k)] at heq
  exact heq

end
end Sude
