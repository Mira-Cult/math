import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18279)) 334102573 334135341 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 334102573 334135341).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18279 334102573 334135341
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18280)) 334135341 334168109 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334135341 334168109).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18280 334135341 334168109
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18281)) 334168109 334200877 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334168109 334200877).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18281 334168109 334200877
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18282)) 334200877 334233645 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334200877 334233645).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18282 334200877 334233645
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 334102573 334168109).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 334102573 ≤ 334135341)
    (by decide : 334135341 ≤ 334168109) block0 block1

theorem join_0_1 : (twinPrimeSegment 334168109 334233645).card = 230 := by
  simpa using combineTwinPrimeSegments (by decide : 334168109 ≤ 334200877)
    (by decide : 334200877 ≤ 334233645) block2 block3

theorem join_1_0 : (twinPrimeSegment 334102573 334233645).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 334102573 ≤ 334168109)
    (by decide : 334168109 ≤ 334233645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 334102573 334233645).card = 460 := join_1_0

end S159C05
end Sude.GeneratedTwinScan
