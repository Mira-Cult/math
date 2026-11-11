import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 66977837 67010605 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 66977837 67010605).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 66977837 67010605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67010605 67043373 = 144 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 67010605 67043373).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67010605 67043373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67043373 67076141 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 67043373 67076141).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67043373 67076141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 67076141 67108909 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 67076141 67108909).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 67076141 67108909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 66977837 67043373).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 66977837 ≤ 67010605)
    (by decide : 67010605 ≤ 67043373) block0 block1

theorem join_0_1 : (twinPrimeSegment 67043373 67108909).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 67043373 ≤ 67076141)
    (by decide : 67076141 ≤ 67108909) block2 block3

theorem join_1_0 : (twinPrimeSegment 66977837 67108909).card = 545 := by
  simpa using combineTwinPrimeSegments (by decide : 66977837 ≤ 67043373)
    (by decide : 67043373 ≤ 67108909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 66977837 67108909).card = 545 := join_1_0

end S031C15
end Sude.GeneratedTwinScan
