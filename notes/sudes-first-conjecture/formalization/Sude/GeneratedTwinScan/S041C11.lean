import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87425069 87457837 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 87425069 87457837).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87425069 87457837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87457837 87490605 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 87457837 87490605).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87457837 87490605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87490605 87523373 = 142 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 87490605 87523373).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87490605 87523373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 87523373 87556141 = 147 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 87523373 87556141).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 87523373 87556141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 87425069 87490605).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 87425069 ≤ 87457837)
    (by decide : 87457837 ≤ 87490605) block0 block1

theorem join_0_1 : (twinPrimeSegment 87490605 87556141).card = 289 := by
  simpa using combineTwinPrimeSegments (by decide : 87490605 ≤ 87523373)
    (by decide : 87523373 ≤ 87556141) block2 block3

theorem join_1_0 : (twinPrimeSegment 87425069 87556141).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 87425069 ≤ 87490605)
    (by decide : 87490605 ≤ 87556141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 87425069 87556141).card = 553 := join_1_0

end S041C11
end Sude.GeneratedTwinScan
