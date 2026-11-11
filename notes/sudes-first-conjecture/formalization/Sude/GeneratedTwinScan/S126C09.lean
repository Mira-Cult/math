import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S126C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16292)) 265420845 265453613 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 265420845 265453613).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16292 265420845 265453613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16293)) 265453613 265486381 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 265453613 265486381).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16293 265453613 265486381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16294)) 265486381 265519149 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 265486381 265519149).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16294 265486381 265519149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16295)) 265519149 265551917 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 265519149 265551917).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16295 265519149 265551917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 265420845 265486381).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 265420845 ≤ 265453613)
    (by decide : 265453613 ≤ 265486381) block0 block1

theorem join_0_1 : (twinPrimeSegment 265486381 265551917).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 265486381 ≤ 265519149)
    (by decide : 265519149 ≤ 265551917) block2 block3

theorem join_1_0 : (twinPrimeSegment 265420845 265551917).card = 464 := by
  simpa using combineTwinPrimeSegments (by decide : 265420845 ≤ 265486381)
    (by decide : 265486381 ≤ 265551917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 265420845 265551917).card = 464 := join_1_0

end S126C09
end Sude.GeneratedTwinScan
