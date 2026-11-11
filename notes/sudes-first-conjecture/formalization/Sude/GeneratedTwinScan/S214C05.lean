import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21200)) 449445933 449478701 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449445933 449478701).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21200 449445933 449478701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21201)) 449478701 449511469 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 449478701 449511469).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21201 449478701 449511469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21202)) 449511469 449544237 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 449511469 449544237).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21202 449511469 449544237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21203)) 449544237 449577005 = 134 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449544237 449577005).card = 134 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21203 449544237 449577005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449445933 449511469).card = 225 := by
  simpa using combineTwinPrimeSegments (by decide : 449445933 ≤ 449478701)
    (by decide : 449478701 ≤ 449511469) block0 block1

theorem join_0_1 : (twinPrimeSegment 449511469 449577005).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 449511469 ≤ 449544237)
    (by decide : 449544237 ≤ 449577005) block2 block3

theorem join_1_0 : (twinPrimeSegment 449445933 449577005).card = 471 := by
  simpa using combineTwinPrimeSegments (by decide : 449445933 ≤ 449511469)
    (by decide : 449511469 ≤ 449577005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449445933 449577005).card = 471 := join_1_0

end S214C05
end Sude.GeneratedTwinScan
