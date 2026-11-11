import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S130C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16532)) 273285165 273317933 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 273285165 273317933).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16532 273285165 273317933
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16533)) 273317933 273350701 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 273317933 273350701).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16533 273317933 273350701
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16534)) 273350701 273383469 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 273350701 273383469).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16534 273350701 273383469
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16535)) 273383469 273416237 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 273383469 273416237).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16535 273383469 273416237
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 273285165 273350701).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 273285165 ≤ 273317933)
    (by decide : 273317933 ≤ 273350701) block0 block1

theorem join_0_1 : (twinPrimeSegment 273350701 273416237).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 273350701 ≤ 273383469)
    (by decide : 273383469 ≤ 273416237) block2 block3

theorem join_1_0 : (twinPrimeSegment 273285165 273416237).card = 479 := by
  simpa using combineTwinPrimeSegments (by decide : 273285165 ≤ 273350701)
    (by decide : 273350701 ≤ 273416237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 273285165 273416237).card = 479 := join_1_0

end S130C05
end Sude.GeneratedTwinScan
