import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S212C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21126)) 446300205 446332973 = 98 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 446300205 446332973).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21126 446300205 446332973
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21127)) 446332973 446365741 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 446332973 446365741).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21127 446332973 446365741
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21128)) 446365741 446398509 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 446365741 446398509).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21128 446365741 446398509
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21128)) 446398509 446431277 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 446398509 446431277).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21128 446398509 446431277
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 446300205 446365741).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 446300205 ≤ 446332973)
    (by decide : 446332973 ≤ 446365741) block0 block1

theorem join_0_1 : (twinPrimeSegment 446365741 446431277).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 446365741 ≤ 446398509)
    (by decide : 446398509 ≤ 446431277) block2 block3

theorem join_1_0 : (twinPrimeSegment 446300205 446431277).card = 448 := by
  simpa using combineTwinPrimeSegments (by decide : 446300205 ≤ 446365741)
    (by decide : 446365741 ≤ 446431277) join_0_0 join_0_1

theorem total : (twinPrimeSegment 446300205 446431277).card = 448 := join_1_0

end S212C13
end Sude.GeneratedTwinScan
