import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S155C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18077)) 326762541 326795309 = 116 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 326762541 326795309).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18077 326762541 326795309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18078)) 326795309 326828077 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 326795309 326828077).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18078 326795309 326828077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18079)) 326828077 326860845 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 326828077 326860845).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18079 326828077 326860845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18080)) 326860845 326893613 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 326860845 326893613).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18080 326860845 326893613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 326762541 326828077).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 326762541 ≤ 326795309)
    (by decide : 326795309 ≤ 326828077) block0 block1

theorem join_0_1 : (twinPrimeSegment 326828077 326893613).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 326828077 ≤ 326860845)
    (by decide : 326860845 ≤ 326893613) block2 block3

theorem join_1_0 : (twinPrimeSegment 326762541 326893613).card = 461 := by
  simpa using combineTwinPrimeSegments (by decide : 326762541 ≤ 326828077)
    (by decide : 326828077 ≤ 326893613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 326762541 326893613).card = 461 := join_1_0

end S155C13
end Sude.GeneratedTwinScan
