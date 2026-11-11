import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69337133 69369901 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 69337133 69369901).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69337133 69369901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69369901 69402669 = 143 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 69369901 69402669).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69369901 69402669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69402669 69435437 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 69402669 69435437).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69402669 69435437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 69435437 69468205 = 150 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 69435437 69468205).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 69435437 69468205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 69337133 69402669).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 69337133 ≤ 69369901)
    (by decide : 69369901 ≤ 69402669) block0 block1

theorem join_0_1 : (twinPrimeSegment 69402669 69468205).card = 272 := by
  simpa using combineTwinPrimeSegments (by decide : 69402669 ≤ 69435437)
    (by decide : 69435437 ≤ 69468205) block2 block3

theorem join_1_0 : (twinPrimeSegment 69337133 69468205).card = 554 := by
  simpa using combineTwinPrimeSegments (by decide : 69337133 ≤ 69402669)
    (by decide : 69402669 ≤ 69468205) join_0_0 join_0_1

theorem total : (twinPrimeSegment 69337133 69468205).card = 554 := join_1_0

end S033C01
end Sude.GeneratedTwinScan
