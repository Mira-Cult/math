import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S200C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20519)) 421003309 421036077 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 421003309 421036077).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20519 421003309 421036077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20519)) 421036077 421068845 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 421036077 421068845).card = 132 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20519 421036077 421068845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20520)) 421068845 421101613 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 421068845 421101613).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20520 421068845 421101613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20521)) 421101613 421134381 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 421101613 421134381).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20521 421101613 421134381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 421003309 421068845).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 421003309 ≤ 421036077)
    (by decide : 421036077 ≤ 421068845) block0 block1

theorem join_0_1 : (twinPrimeSegment 421068845 421134381).card = 208 := by
  simpa using combineTwinPrimeSegments (by decide : 421068845 ≤ 421101613)
    (by decide : 421101613 ≤ 421134381) block2 block3

theorem join_1_0 : (twinPrimeSegment 421003309 421134381).card = 447 := by
  simpa using combineTwinPrimeSegments (by decide : 421003309 ≤ 421068845)
    (by decide : 421068845 ≤ 421134381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 421003309 421134381).card = 447 := join_1_0

end S200C12
end Sude.GeneratedTwinScan
