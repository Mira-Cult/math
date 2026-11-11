import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S181C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19497)) 380108845 380141613 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 380108845 380141613).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19497 380108845 380141613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19498)) 380141613 380174381 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 380141613 380174381).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19498 380141613 380174381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19498)) 380174381 380207149 = 103 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 380174381 380207149).card = 103 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19498 380174381 380207149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19499)) 380207149 380239917 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 380207149 380239917).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19499 380207149 380239917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 380108845 380174381).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 380108845 ≤ 380141613)
    (by decide : 380141613 ≤ 380174381) block0 block1

theorem join_0_1 : (twinPrimeSegment 380174381 380239917).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 380174381 ≤ 380207149)
    (by decide : 380207149 ≤ 380239917) block2 block3

theorem join_1_0 : (twinPrimeSegment 380108845 380239917).card = 458 := by
  simpa using combineTwinPrimeSegments (by decide : 380108845 ≤ 380174381)
    (by decide : 380174381 ≤ 380239917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 380108845 380239917).card = 458 := join_1_0

end S181C04
end Sude.GeneratedTwinScan
