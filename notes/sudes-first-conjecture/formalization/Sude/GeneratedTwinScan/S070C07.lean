import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147718189 147750957 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 147718189 147750957).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147718189 147750957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147750957 147783725 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 147750957 147783725).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147750957 147783725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147783725 147816493 = 106 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 147783725 147816493).card = 106 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147783725 147816493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 147816493 147849261 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 147816493 147849261).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 147816493 147849261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 147718189 147783725).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 147718189 ≤ 147750957)
    (by decide : 147750957 ≤ 147783725) block0 block1

theorem join_0_1 : (twinPrimeSegment 147783725 147849261).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 147783725 ≤ 147816493)
    (by decide : 147816493 ≤ 147849261) block2 block3

theorem join_1_0 : (twinPrimeSegment 147718189 147849261).card = 469 := by
  simpa using combineTwinPrimeSegments (by decide : 147718189 ≤ 147783725)
    (by decide : 147783725 ≤ 147849261) join_0_0 join_0_1

theorem total : (twinPrimeSegment 147718189 147849261).card = 469 := join_1_0

end S070C07
end Sude.GeneratedTwinScan
