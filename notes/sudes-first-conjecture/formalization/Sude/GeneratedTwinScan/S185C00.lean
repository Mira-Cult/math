import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S185C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19697)) 387973165 388005933 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 387973165 388005933).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19697 387973165 388005933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19698)) 388005933 388038701 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 388005933 388038701).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19698 388005933 388038701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19699)) 388038701 388071469 = 98 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 388038701 388071469).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19699 388038701 388071469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19700)) 388071469 388104237 = 80 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 388071469 388104237).card = 80 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19700 388071469 388104237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 387973165 388038701).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 387973165 ≤ 388005933)
    (by decide : 388005933 ≤ 388038701) block0 block1

theorem join_0_1 : (twinPrimeSegment 388038701 388104237).card = 178 := by
  simpa using combineTwinPrimeSegments (by decide : 388038701 ≤ 388071469)
    (by decide : 388071469 ≤ 388104237) block2 block3

theorem join_1_0 : (twinPrimeSegment 387973165 388104237).card = 410 := by
  simpa using combineTwinPrimeSegments (by decide : 387973165 ≤ 388038701)
    (by decide : 388038701 ≤ 388104237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 387973165 388104237).card = 410 := join_1_0

end S185C00
end Sude.GeneratedTwinScan
