import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146669613 146702381 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 146669613 146702381).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146669613 146702381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146702381 146735149 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 146702381 146735149).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146702381 146735149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146735149 146767917 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 146735149 146767917).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146735149 146767917
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 146767917 146800685 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 146767917 146800685).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 146767917 146800685
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 146669613 146735149).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 146669613 ≤ 146702381)
    (by decide : 146702381 ≤ 146735149) block0 block1

theorem join_0_1 : (twinPrimeSegment 146735149 146800685).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 146735149 ≤ 146767917)
    (by decide : 146767917 ≤ 146800685) block2 block3

theorem join_1_0 : (twinPrimeSegment 146669613 146800685).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 146669613 ≤ 146735149)
    (by decide : 146735149 ≤ 146800685) join_0_0 join_0_1

theorem total : (twinPrimeSegment 146669613 146800685).card = 498 := join_1_0

end S069C15
end Sude.GeneratedTwinScan
