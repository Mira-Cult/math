import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61603885 61636653 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 61603885 61636653).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61603885 61636653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61636653 61669421 = 151 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 61636653 61669421).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61636653 61669421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61669421 61702189 = 149 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 61669421 61702189).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61669421 61702189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61702189 61734957 = 149 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 61702189 61734957).card = 149 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61702189 61734957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 61603885 61669421).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 61603885 ≤ 61636653)
    (by decide : 61636653 ≤ 61669421) block0 block1

theorem join_0_1 : (twinPrimeSegment 61669421 61734957).card = 298 := by
  simpa using combineTwinPrimeSegments (by decide : 61669421 ≤ 61702189)
    (by decide : 61702189 ≤ 61734957) block2 block3

theorem join_1_0 : (twinPrimeSegment 61603885 61734957).card = 580 := by
  simpa using combineTwinPrimeSegments (by decide : 61603885 ≤ 61669421)
    (by decide : 61669421 ≤ 61734957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 61603885 61734957).card = 580 := join_1_0

end S029C06
end Sude.GeneratedTwinScan
