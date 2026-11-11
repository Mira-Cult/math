import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S238C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22374)) 500564013 500596781 = 100 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 500564013 500596781).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22374 500564013 500596781
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22374)) 500596781 500629549 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 500596781 500629549).card = 104 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22374 500596781 500629549
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22375)) 500629549 500662317 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 500629549 500662317).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22375 500629549 500662317
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22376)) 500662317 500695085 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 500662317 500695085).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22376 500662317 500695085
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 500564013 500629549).card = 204 := by
  simpa using combineTwinPrimeSegments (by decide : 500564013 ≤ 500596781)
    (by decide : 500596781 ≤ 500629549) block0 block1

theorem join_0_1 : (twinPrimeSegment 500629549 500695085).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 500629549 ≤ 500662317)
    (by decide : 500662317 ≤ 500695085) block2 block3

theorem join_1_0 : (twinPrimeSegment 500564013 500695085).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 500564013 ≤ 500629549)
    (by decide : 500629549 ≤ 500695085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 500564013 500695085).card = 426 := join_1_0

end S238C11
end Sude.GeneratedTwinScan
