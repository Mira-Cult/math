import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S163C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18528)) 343277613 343310381 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 343277613 343310381).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18528 343277613 343310381
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18529)) 343310381 343343149 = 85 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 343310381 343343149).card = 85 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18529 343310381 343343149
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18530)) 343343149 343375917 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 343343149 343375917).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18530 343343149 343375917
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18531)) 343375917 343408685 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 343375917 343408685).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18531 343375917 343408685
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 343277613 343343149).card = 188 := by
  simpa using combineTwinPrimeSegments (by decide : 343277613 ≤ 343310381)
    (by decide : 343310381 ≤ 343343149) block0 block1

theorem join_0_1 : (twinPrimeSegment 343343149 343408685).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 343343149 ≤ 343375917)
    (by decide : 343375917 ≤ 343408685) block2 block3

theorem join_1_0 : (twinPrimeSegment 343277613 343408685).card = 405 := by
  simpa using combineTwinPrimeSegments (by decide : 343277613 ≤ 343343149)
    (by decide : 343343149 ≤ 343408685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 343277613 343408685).card = 405 := join_1_0

end S163C11
end Sude.GeneratedTwinScan
