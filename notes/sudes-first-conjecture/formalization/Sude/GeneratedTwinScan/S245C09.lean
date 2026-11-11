import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22693)) 514981933 515014701 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 514981933 515014701).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22693 514981933 515014701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22694)) 515014701 515047469 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515014701 515047469).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22694 515014701 515047469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22695)) 515047469 515080237 = 99 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515047469 515080237).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22695 515047469 515080237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22696)) 515080237 515113005 = 105 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515080237 515113005).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22696 515080237 515113005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 514981933 515047469).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 514981933 ≤ 515014701)
    (by decide : 515014701 ≤ 515047469) block0 block1

theorem join_0_1 : (twinPrimeSegment 515047469 515113005).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 515047469 ≤ 515080237)
    (by decide : 515080237 ≤ 515113005) block2 block3

theorem join_1_0 : (twinPrimeSegment 514981933 515113005).card = 423 := by
  simpa using combineTwinPrimeSegments (by decide : 514981933 ≤ 515047469)
    (by decide : 515047469 ≤ 515113005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 514981933 515113005).card = 423 := join_1_0

end S245C09
end Sude.GeneratedTwinScan
