import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129368109 129400877 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 129368109 129400877).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129368109 129400877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129400877 129433645 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129400877 129433645).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129400877 129433645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129433645 129466413 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129433645 129466413).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129433645 129466413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129466413 129499181 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129466413 129499181).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129466413 129499181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 129368109 129433645).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 129368109 ≤ 129400877)
    (by decide : 129400877 ≤ 129433645) block0 block1

theorem join_0_1 : (twinPrimeSegment 129433645 129499181).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 129433645 ≤ 129466413)
    (by decide : 129466413 ≤ 129499181) block2 block3

theorem join_1_0 : (twinPrimeSegment 129368109 129499181).card = 503 := by
  simpa using combineTwinPrimeSegments (by decide : 129368109 ≤ 129433645)
    (by decide : 129433645 ≤ 129499181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 129368109 129499181).card = 503 := join_1_0

end S061C11
end Sude.GeneratedTwinScan
