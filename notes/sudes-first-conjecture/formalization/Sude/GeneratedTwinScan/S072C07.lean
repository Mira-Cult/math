import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151912493 151945261 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 151912493 151945261).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151912493 151945261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151945261 151978029 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 151945261 151978029).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151945261 151978029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 151978029 152010797 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 151978029 152010797).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 151978029 152010797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152010797 152043565 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 152010797 152043565).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152010797 152043565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 151912493 151978029).card = 252 := by
  simpa using combineTwinPrimeSegments (by decide : 151912493 ≤ 151945261)
    (by decide : 151945261 ≤ 151978029) block0 block1

theorem join_0_1 : (twinPrimeSegment 151978029 152043565).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 151978029 ≤ 152010797)
    (by decide : 152010797 ≤ 152043565) block2 block3

theorem join_1_0 : (twinPrimeSegment 151912493 152043565).card = 492 := by
  simpa using combineTwinPrimeSegments (by decide : 151912493 ≤ 151978029)
    (by decide : 151978029 ≤ 152043565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 151912493 152043565).card = 492 := join_1_0

end S072C07
end Sude.GeneratedTwinScan
