import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128450605 128483373 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128450605 128483373).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128450605 128483373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128483373 128516141 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 128483373 128516141).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128483373 128516141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128516141 128548909 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 128516141 128548909).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128516141 128548909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128548909 128581677 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128548909 128581677).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128548909 128581677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128450605 128516141).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 128450605 ≤ 128483373)
    (by decide : 128483373 ≤ 128516141) block0 block1

theorem join_0_1 : (twinPrimeSegment 128516141 128581677).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 128516141 ≤ 128548909)
    (by decide : 128548909 ≤ 128581677) block2 block3

theorem join_1_0 : (twinPrimeSegment 128450605 128581677).card = 516 := by
  simpa using combineTwinPrimeSegments (by decide : 128450605 ≤ 128516141)
    (by decide : 128516141 ≤ 128581677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128450605 128581677).card = 516 := join_1_0

end S061C04
end Sude.GeneratedTwinScan
