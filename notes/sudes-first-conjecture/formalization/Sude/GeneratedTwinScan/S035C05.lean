import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74055725 74088493 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 74055725 74088493).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74055725 74088493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74088493 74121261 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 74088493 74121261).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74088493 74121261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74121261 74154029 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 74121261 74154029).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74121261 74154029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 74154029 74186797 = 122 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 74154029 74186797).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 74154029 74186797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 74055725 74121261).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 74055725 ≤ 74088493)
    (by decide : 74088493 ≤ 74121261) block0 block1

theorem join_0_1 : (twinPrimeSegment 74121261 74186797).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 74121261 ≤ 74154029)
    (by decide : 74154029 ≤ 74186797) block2 block3

theorem join_1_0 : (twinPrimeSegment 74055725 74186797).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 74055725 ≤ 74121261)
    (by decide : 74121261 ≤ 74186797) join_0_0 join_0_1

theorem total : (twinPrimeSegment 74055725 74186797).card = 511 := join_1_0

end S035C05
end Sude.GeneratedTwinScan
