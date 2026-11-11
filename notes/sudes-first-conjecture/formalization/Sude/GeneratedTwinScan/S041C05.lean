import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S041C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86638637 86671405 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 86638637 86671405).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86638637 86671405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86671405 86704173 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 86671405 86704173).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86671405 86704173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86704173 86736941 = 143 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 86704173 86736941).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86704173 86736941
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 86736941 86769709 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 86736941 86769709).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 86736941 86769709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 86638637 86704173).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 86638637 ≤ 86671405)
    (by decide : 86671405 ≤ 86704173) block0 block1

theorem join_0_1 : (twinPrimeSegment 86704173 86769709).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 86704173 ≤ 86736941)
    (by decide : 86736941 ≤ 86769709) block2 block3

theorem join_1_0 : (twinPrimeSegment 86638637 86769709).card = 513 := by
  simpa using combineTwinPrimeSegments (by decide : 86638637 ≤ 86704173)
    (by decide : 86704173 ≤ 86769709) join_0_0 join_0_1

theorem total : (twinPrimeSegment 86638637 86769709).card = 513 := join_1_0

end S041C05
end Sude.GeneratedTwinScan
