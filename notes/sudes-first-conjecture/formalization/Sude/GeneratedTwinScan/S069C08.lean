import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145752109 145784877 = 103 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 145752109 145784877).card = 103 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145752109 145784877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145784877 145817645 = 138 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 145784877 145817645).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145784877 145817645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145817645 145850413 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145817645 145850413).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145817645 145850413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145850413 145883181 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145850413 145883181).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145850413 145883181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 145752109 145817645).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 145752109 ≤ 145784877)
    (by decide : 145784877 ≤ 145817645) block0 block1

theorem join_0_1 : (twinPrimeSegment 145817645 145883181).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 145817645 ≤ 145850413)
    (by decide : 145850413 ≤ 145883181) block2 block3

theorem join_1_0 : (twinPrimeSegment 145752109 145883181).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 145752109 ≤ 145817645)
    (by decide : 145817645 ≤ 145883181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 145752109 145883181).card = 484 := join_1_0

end S069C08
end Sude.GeneratedTwinScan
