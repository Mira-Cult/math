import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S122C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16037)) 257163309 257196077 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 257163309 257196077).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16037 257163309 257196077
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16038)) 257196077 257228845 = 100 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 257196077 257228845).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16038 257196077 257228845
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16039)) 257228845 257261613 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 257228845 257261613).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16039 257228845 257261613
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16040)) 257261613 257294381 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 257261613 257294381).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16040 257261613 257294381
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 257163309 257228845).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 257163309 ≤ 257196077)
    (by decide : 257196077 ≤ 257228845) block0 block1

theorem join_0_1 : (twinPrimeSegment 257228845 257294381).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 257228845 ≤ 257261613)
    (by decide : 257261613 ≤ 257294381) block2 block3

theorem join_1_0 : (twinPrimeSegment 257163309 257294381).card = 442 := by
  simpa using combineTwinPrimeSegments (by decide : 257163309 ≤ 257228845)
    (by decide : 257228845 ≤ 257294381) join_0_0 join_0_1

theorem total : (twinPrimeSegment 257163309 257294381).card = 442 := join_1_0

end S122C10
end Sude.GeneratedTwinScan
