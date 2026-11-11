import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109445165 109477933 = 139 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109445165 109477933).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109445165 109477933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109477933 109510701 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 109477933 109510701).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109477933 109510701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109510701 109543469 = 104 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 109510701 109543469).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109510701 109543469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109543469 109576237 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109543469 109576237).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109543469 109576237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109445165 109510701).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 109445165 ≤ 109477933)
    (by decide : 109477933 ≤ 109510701) block0 block1

theorem join_0_1 : (twinPrimeSegment 109510701 109576237).card = 231 := by
  simpa using combineTwinPrimeSegments (by decide : 109510701 ≤ 109543469)
    (by decide : 109543469 ≤ 109576237) block2 block3

theorem join_1_0 : (twinPrimeSegment 109445165 109576237).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 109445165 ≤ 109510701)
    (by decide : 109510701 ≤ 109576237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109445165 109576237).card = 492 := join_1_0

end S052C03
end Sude.GeneratedTwinScan
