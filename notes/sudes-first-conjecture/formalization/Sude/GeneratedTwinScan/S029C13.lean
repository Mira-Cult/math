import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62521389 62554157 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 62521389 62554157).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62521389 62554157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62554157 62586925 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62554157 62586925).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62554157 62586925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62586925 62619693 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62586925 62619693).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62586925 62619693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62619693 62652461 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 62619693 62652461).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62619693 62652461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 62521389 62586925).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 62521389 ≤ 62554157)
    (by decide : 62554157 ≤ 62586925) block0 block1

theorem join_0_1 : (twinPrimeSegment 62586925 62652461).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 62586925 ≤ 62619693)
    (by decide : 62619693 ≤ 62652461) block2 block3

theorem join_1_0 : (twinPrimeSegment 62521389 62652461).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 62521389 ≤ 62586925)
    (by decide : 62586925 ≤ 62652461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 62521389 62652461).card = 502 := join_1_0

end S029C13
end Sude.GeneratedTwinScan
