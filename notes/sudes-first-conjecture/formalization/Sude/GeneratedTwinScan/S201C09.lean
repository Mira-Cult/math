import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S201C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20560)) 422707245 422740013 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 422707245 422740013).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20560 422707245 422740013
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20561)) 422740013 422772781 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 422740013 422772781).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20561 422740013 422772781
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20562)) 422772781 422805549 = 76 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 422772781 422805549).card = 76 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20562 422772781 422805549
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 20563)) 422805549 422838317 = 102 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 422805549 422838317).card = 102 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 20563 422805549 422838317
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 422707245 422772781).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 422707245 ≤ 422740013)
    (by decide : 422740013 ≤ 422772781) block0 block1

theorem join_0_1 : (twinPrimeSegment 422772781 422838317).card = 178 := by
  simpa using combineTwinPrimeSegments (by decide : 422772781 ≤ 422805549)
    (by decide : 422805549 ≤ 422838317) block2 block3

theorem join_1_0 : (twinPrimeSegment 422707245 422838317).card = 401 := by
  simpa using combineTwinPrimeSegments (by decide : 422707245 ≤ 422772781)
    (by decide : 422772781 ≤ 422838317) join_0_0 join_0_1

theorem total : (twinPrimeSegment 422707245 422838317).card = 401 := join_1_0

end S201C09
end Sude.GeneratedTwinScan
