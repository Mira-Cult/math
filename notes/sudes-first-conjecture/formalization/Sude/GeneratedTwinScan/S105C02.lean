import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S105C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14849)) 220463149 220495917 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 220463149 220495917).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14849 220463149 220495917
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14850)) 220495917 220528685 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 220495917 220528685).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14850 220495917 220528685
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14851)) 220528685 220561453 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 220528685 220561453).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14851 220528685 220561453
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14852)) 220561453 220594221 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 220561453 220594221).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14852 220561453 220594221
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 220463149 220528685).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 220463149 ≤ 220495917)
    (by decide : 220495917 ≤ 220528685) block0 block1

theorem join_0_1 : (twinPrimeSegment 220528685 220594221).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 220528685 ≤ 220561453)
    (by decide : 220561453 ≤ 220594221) block2 block3

theorem join_1_0 : (twinPrimeSegment 220463149 220594221).card = 453 := by
  simpa using combineTwinPrimeSegments (by decide : 220463149 ≤ 220528685)
    (by decide : 220528685 ≤ 220594221) join_0_0 join_0_1

theorem total : (twinPrimeSegment 220463149 220594221).card = 453 := join_1_0

end S105C02
end Sude.GeneratedTwinScan
