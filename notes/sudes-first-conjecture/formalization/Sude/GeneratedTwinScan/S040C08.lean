import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84934701 84967469 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84934701 84967469).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84934701 84967469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84967469 85000237 = 112 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84967469 85000237).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84967469 85000237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85000237 85033005 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 85000237 85033005).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85000237 85033005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 85033005 85065773 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 85033005 85065773).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 85033005 85065773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84934701 85000237).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 84934701 ≤ 84967469)
    (by decide : 84967469 ≤ 85000237) block0 block1

theorem join_0_1 : (twinPrimeSegment 85000237 85065773).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 85000237 ≤ 85033005)
    (by decide : 85033005 ≤ 85065773) block2 block3

theorem join_1_0 : (twinPrimeSegment 84934701 85065773).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 84934701 ≤ 85000237)
    (by decide : 85000237 ≤ 85065773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84934701 85065773).card = 477 := join_1_0

end S040C08
end Sude.GeneratedTwinScan
