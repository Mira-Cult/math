import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S046C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98041901 98074669 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 98041901 98074669).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98041901 98074669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98074669 98107437 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 98074669 98107437).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98074669 98107437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98107437 98140205 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 98107437 98140205).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98107437 98140205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 98140205 98172973 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 98140205 98172973).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 98140205 98172973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 98041901 98107437).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 98041901 ≤ 98074669)
    (by decide : 98074669 ≤ 98107437) block0 block1

theorem join_0_1 : (twinPrimeSegment 98107437 98172973).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 98107437 ≤ 98140205)
    (by decide : 98140205 ≤ 98172973) block2 block3

theorem join_1_0 : (twinPrimeSegment 98041901 98172973).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 98041901 ≤ 98107437)
    (by decide : 98107437 ≤ 98172973) join_0_0 join_0_1

theorem total : (twinPrimeSegment 98041901 98172973).card = 499 := join_1_0

end S046C12
end Sude.GeneratedTwinScan
