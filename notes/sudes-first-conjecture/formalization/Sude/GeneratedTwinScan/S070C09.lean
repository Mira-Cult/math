import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147980333 148013101 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147980333 148013101).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147980333 148013101
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148013101 148045869 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148013101 148045869).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148013101 148045869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148045869 148078637 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148045869 148078637).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148045869 148078637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148078637 148111405 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148078637 148111405).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148078637 148111405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147980333 148045869).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 147980333 ≤ 148013101)
    (by decide : 148013101 ≤ 148045869) block0 block1

theorem join_0_1 : (twinPrimeSegment 148045869 148111405).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 148045869 ≤ 148078637)
    (by decide : 148078637 ≤ 148111405) block2 block3

theorem join_1_0 : (twinPrimeSegment 147980333 148111405).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 147980333 ≤ 148045869)
    (by decide : 148045869 ≤ 148111405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147980333 148111405).card = 488 := join_1_0

end S070C09
end Sude.GeneratedTwinScan
