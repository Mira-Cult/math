import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126222381 126255149 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 126222381 126255149).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126222381 126255149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126255149 126287917 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 126255149 126287917).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126255149 126287917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126287917 126320685 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 126287917 126320685).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126287917 126320685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 126320685 126353453 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 126320685 126353453).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 126320685 126353453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 126222381 126287917).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 126222381 ≤ 126255149)
    (by decide : 126255149 ≤ 126287917) block0 block1

theorem join_0_1 : (twinPrimeSegment 126287917 126353453).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 126287917 ≤ 126320685)
    (by decide : 126320685 ≤ 126353453) block2 block3

theorem join_1_0 : (twinPrimeSegment 126222381 126353453).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 126222381 ≤ 126287917)
    (by decide : 126287917 ≤ 126353453) join_0_0 join_0_1

theorem total : (twinPrimeSegment 126222381 126353453).card = 504 := join_1_0

end S060C03
end Sude.GeneratedTwinScan
