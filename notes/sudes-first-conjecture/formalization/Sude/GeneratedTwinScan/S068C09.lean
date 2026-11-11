import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143786029 143818797 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 143786029 143818797).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143786029 143818797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143818797 143851565 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143818797 143851565).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143818797 143851565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143851565 143884333 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143851565 143884333).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143851565 143884333
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143884333 143917101 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 143884333 143917101).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143884333 143917101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 143786029 143851565).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 143786029 ≤ 143818797)
    (by decide : 143818797 ≤ 143851565) block0 block1

theorem join_0_1 : (twinPrimeSegment 143851565 143917101).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 143851565 ≤ 143884333)
    (by decide : 143884333 ≤ 143917101) block2 block3

theorem join_1_0 : (twinPrimeSegment 143786029 143917101).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 143786029 ≤ 143851565)
    (by decide : 143851565 ≤ 143917101) join_0_0 join_0_1

theorem total : (twinPrimeSegment 143786029 143917101).card = 495 := join_1_0

end S068C09
end Sude.GeneratedTwinScan
