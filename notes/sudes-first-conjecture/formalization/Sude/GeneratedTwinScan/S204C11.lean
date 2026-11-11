import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S204C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20719)) 429260845 429293613 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 429260845 429293613).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20719 429260845 429293613
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20720)) 429293613 429326381 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 429293613 429326381).card = 123 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20720 429293613 429326381
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20720)) 429326381 429359149 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 429326381 429359149).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20720 429326381 429359149
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20721)) 429359149 429391917 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 429359149 429391917).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20721 429359149 429391917
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 429260845 429326381).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 429260845 ≤ 429293613)
    (by decide : 429293613 ≤ 429326381) block0 block1

theorem join_0_1 : (twinPrimeSegment 429326381 429391917).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 429326381 ≤ 429359149)
    (by decide : 429359149 ≤ 429391917) block2 block3

theorem join_1_0 : (twinPrimeSegment 429260845 429391917).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 429260845 ≤ 429326381)
    (by decide : 429326381 ≤ 429391917) join_0_0 join_0_1

theorem total : (twinPrimeSegment 429260845 429391917).card = 472 := join_1_0

end S204C11
end Sude.GeneratedTwinScan
