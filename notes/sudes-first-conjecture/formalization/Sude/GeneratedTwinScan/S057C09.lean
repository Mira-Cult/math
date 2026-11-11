import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120717357 120750125 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120717357 120750125).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120717357 120750125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120750125 120782893 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 120750125 120782893).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120750125 120782893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120782893 120815661 = 102 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 120782893 120815661).card = 102 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120782893 120815661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120815661 120848429 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120815661 120848429).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120815661 120848429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120717357 120782893).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 120717357 ≤ 120750125)
    (by decide : 120750125 ≤ 120782893) block0 block1

theorem join_0_1 : (twinPrimeSegment 120782893 120848429).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 120782893 ≤ 120815661)
    (by decide : 120815661 ≤ 120848429) block2 block3

theorem join_1_0 : (twinPrimeSegment 120717357 120848429).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 120717357 ≤ 120782893)
    (by decide : 120782893 ≤ 120848429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120717357 120848429).card = 467 := join_1_0

end S057C09
end Sude.GeneratedTwinScan
