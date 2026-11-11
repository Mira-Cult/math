import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102105133 102137901 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 102105133 102137901).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102105133 102137901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102137901 102170669 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102137901 102170669).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102137901 102170669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102170669 102203437 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102170669 102203437).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102170669 102203437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102203437 102236205 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102203437 102236205).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102203437 102236205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 102105133 102170669).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 102105133 ≤ 102137901)
    (by decide : 102137901 ≤ 102170669) block0 block1

theorem join_0_1 : (twinPrimeSegment 102170669 102236205).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 102170669 ≤ 102203437)
    (by decide : 102203437 ≤ 102236205) block2 block3

theorem join_1_0 : (twinPrimeSegment 102105133 102236205).card = 506 := by
  simpa using combineTwinPrimeSegments (by decide : 102105133 ≤ 102170669)
    (by decide : 102170669 ≤ 102236205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 102105133 102236205).card = 506 := join_1_0

end S048C11
end Sude.GeneratedTwinScan
