import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S068C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143392813 143425581 = 130 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 143392813 143425581).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143392813 143425581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143425581 143458349 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 143425581 143458349).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143425581 143458349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143458349 143491117 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 143458349 143491117).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143458349 143491117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 143491117 143523885 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 143491117 143523885).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 143491117 143523885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 143392813 143458349).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 143392813 ≤ 143425581)
    (by decide : 143425581 ≤ 143458349) block0 block1

theorem join_0_1 : (twinPrimeSegment 143458349 143523885).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 143458349 ≤ 143491117)
    (by decide : 143491117 ≤ 143523885) block2 block3

theorem join_1_0 : (twinPrimeSegment 143392813 143523885).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 143392813 ≤ 143458349)
    (by decide : 143458349 ≤ 143523885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 143392813 143523885).card = 514 := join_1_0

end S068C06
end Sude.GeneratedTwinScan
