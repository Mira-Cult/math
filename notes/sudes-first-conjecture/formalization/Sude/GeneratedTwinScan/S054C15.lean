import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S054C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115212333 115245101 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 115212333 115245101).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115212333 115245101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115245101 115277869 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 115245101 115277869).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115245101 115277869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115277869 115310637 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 115277869 115310637).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115277869 115310637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115310637 115343405 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 115310637 115343405).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115310637 115343405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 115212333 115277869).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 115212333 ≤ 115245101)
    (by decide : 115245101 ≤ 115277869) block0 block1

theorem join_0_1 : (twinPrimeSegment 115277869 115343405).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 115277869 ≤ 115310637)
    (by decide : 115310637 ≤ 115343405) block2 block3

theorem join_1_0 : (twinPrimeSegment 115212333 115343405).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 115212333 ≤ 115277869)
    (by decide : 115277869 ≤ 115343405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 115212333 115343405).card = 504 := join_1_0

end S054C15
end Sude.GeneratedTwinScan
