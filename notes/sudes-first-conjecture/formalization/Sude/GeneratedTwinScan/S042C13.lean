import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89784365 89817133 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 89784365 89817133).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89784365 89817133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89817133 89849901 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89817133 89849901).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89817133 89849901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89849901 89882669 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89849901 89882669).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89849901 89882669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89882669 89915437 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 89882669 89915437).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89882669 89915437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 89784365 89849901).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 89784365 ≤ 89817133)
    (by decide : 89817133 ≤ 89849901) block0 block1

theorem join_0_1 : (twinPrimeSegment 89849901 89915437).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 89849901 ≤ 89882669)
    (by decide : 89882669 ≤ 89915437) block2 block3

theorem join_1_0 : (twinPrimeSegment 89784365 89915437).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 89784365 ≤ 89849901)
    (by decide : 89849901 ≤ 89915437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 89784365 89915437).card = 505 := join_1_0

end S042C13
end Sude.GeneratedTwinScan
