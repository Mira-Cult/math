import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106037293 106070061 = 143 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106037293 106070061).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106037293 106070061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106070061 106102829 = 136 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106070061 106102829).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106070061 106102829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106102829 106135597 = 125 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 106102829 106135597).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106102829 106135597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106135597 106168365 = 145 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106135597 106168365).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106135597 106168365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106037293 106102829).card = 279 := by
  simpa using combineTwinPrimeSegments (by decide : 106037293 ≤ 106070061)
    (by decide : 106070061 ≤ 106102829) block0 block1

theorem join_0_1 : (twinPrimeSegment 106102829 106168365).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 106102829 ≤ 106135597)
    (by decide : 106135597 ≤ 106168365) block2 block3

theorem join_1_0 : (twinPrimeSegment 106037293 106168365).card = 549 := by
  simpa using combineTwinPrimeSegments (by decide : 106037293 ≤ 106102829)
    (by decide : 106102829 ≤ 106168365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106037293 106168365).card = 549 := join_1_0

end S050C09
end Sude.GeneratedTwinScan
