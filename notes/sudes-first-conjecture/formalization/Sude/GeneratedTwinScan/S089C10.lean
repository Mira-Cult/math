import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13710)) 187957293 187990061 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 187957293 187990061).card = 138 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13710 187957293 187990061
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13712)) 187990061 188022829 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 187990061 188022829).card = 125 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13712 187990061 188022829
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13713)) 188022829 188055597 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 188022829 188055597).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13713 188022829 188055597
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13714)) 188055597 188088365 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 188055597 188088365).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13714 188055597 188088365
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 187957293 188022829).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 187957293 ≤ 187990061)
    (by decide : 187990061 ≤ 188022829) block0 block1

theorem join_0_1 : (twinPrimeSegment 188022829 188088365).card = 235 := by
  simpa using combineTwinPrimeSegments (by decide : 188022829 ≤ 188055597)
    (by decide : 188055597 ≤ 188088365) block2 block3

theorem join_1_0 : (twinPrimeSegment 187957293 188088365).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 187957293 ≤ 188022829)
    (by decide : 188022829 ≤ 188088365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 187957293 188088365).card = 498 := join_1_0

end S089C10
end Sude.GeneratedTwinScan
