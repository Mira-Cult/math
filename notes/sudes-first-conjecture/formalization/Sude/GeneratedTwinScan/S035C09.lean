import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74580013 74612781 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74580013 74612781).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74580013 74612781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74612781 74645549 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 74612781 74645549).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74612781 74645549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74645549 74678317 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 74645549 74678317).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74645549 74678317
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74678317 74711085 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74678317 74711085).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74678317 74711085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74580013 74645549).card = 268 := by
  simpa using combineTwinPrimeSegments (by decide : 74580013 ≤ 74612781)
    (by decide : 74612781 ≤ 74645549) block0 block1

theorem join_0_1 : (twinPrimeSegment 74645549 74711085).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 74645549 ≤ 74678317)
    (by decide : 74678317 ≤ 74711085) block2 block3

theorem join_1_0 : (twinPrimeSegment 74580013 74711085).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 74580013 ≤ 74645549)
    (by decide : 74645549 ≤ 74711085) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74580013 74711085).card = 527 := join_1_0

end S035C09
end Sude.GeneratedTwinScan
