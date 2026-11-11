import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S179C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19402)) 376438829 376471597 = 104 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 376438829 376471597).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19402 376438829 376471597
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19403)) 376471597 376504365 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 376471597 376504365).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19403 376471597 376504365
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19404)) 376504365 376537133 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 376504365 376537133).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19404 376504365 376537133
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19405)) 376537133 376569901 = 106 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 376537133 376569901).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19405 376537133 376569901
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 376438829 376504365).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 376438829 ≤ 376471597)
    (by decide : 376471597 ≤ 376504365) block0 block1

theorem join_0_1 : (twinPrimeSegment 376504365 376569901).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 376504365 ≤ 376537133)
    (by decide : 376537133 ≤ 376569901) block2 block3

theorem join_1_0 : (twinPrimeSegment 376438829 376569901).card = 440 := by
  simpa using combineTwinPrimeSegments (by decide : 376438829 ≤ 376504365)
    (by decide : 376504365 ≤ 376569901) join_0_0 join_0_1

theorem total : (twinPrimeSegment 376438829 376569901).card = 440 := join_1_0

end S179C08
end Sude.GeneratedTwinScan
