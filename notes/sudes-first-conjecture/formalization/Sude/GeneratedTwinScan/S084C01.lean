import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S084C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13278)) 176291885 176324653 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 176291885 176324653).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13278 176291885 176324653
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13279)) 176324653 176357421 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 176324653 176357421).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13279 176324653 176357421
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13281)) 176357421 176390189 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 176357421 176390189).card = 133 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13281 176357421 176390189
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13282)) 176390189 176422957 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 176390189 176422957).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13282 176390189 176422957
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 176291885 176357421).card = 210 := by
  simpa using combineTwinPrimeSegments (by decide : 176291885 ≤ 176324653)
    (by decide : 176324653 ≤ 176357421) block0 block1

theorem join_0_1 : (twinPrimeSegment 176357421 176422957).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 176357421 ≤ 176390189)
    (by decide : 176390189 ≤ 176422957) block2 block3

theorem join_1_0 : (twinPrimeSegment 176291885 176422957).card = 460 := by
  simpa using combineTwinPrimeSegments (by decide : 176291885 ≤ 176357421)
    (by decide : 176357421 ≤ 176422957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 176291885 176422957).card = 460 := join_1_0

end S084C01
end Sude.GeneratedTwinScan
