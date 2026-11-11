import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133431341 133464109 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 133431341 133464109).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133431341 133464109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133464109 133496877 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 133464109 133496877).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133464109 133496877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133496877 133529645 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 133496877 133529645).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133496877 133529645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 133529645 133562413 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 133529645 133562413).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 133529645 133562413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 133431341 133496877).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 133431341 ≤ 133464109)
    (by decide : 133464109 ≤ 133496877) block0 block1

theorem join_0_1 : (twinPrimeSegment 133496877 133562413).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 133496877 ≤ 133529645)
    (by decide : 133529645 ≤ 133562413) block2 block3

theorem join_1_0 : (twinPrimeSegment 133431341 133562413).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 133431341 ≤ 133496877)
    (by decide : 133496877 ≤ 133562413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 133431341 133562413).card = 488 := join_1_0

end S063C10
end Sude.GeneratedTwinScan
