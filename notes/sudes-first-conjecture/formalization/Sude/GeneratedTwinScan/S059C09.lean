import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S059C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124911661 124944429 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 124911661 124944429).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124911661 124944429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124944429 124977197 = 120 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 124944429 124977197).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124944429 124977197
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 124977197 125009965 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 124977197 125009965).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 124977197 125009965
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 125009965 125042733 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 125009965 125042733).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 125009965 125042733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 124911661 124977197).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 124911661 ≤ 124944429)
    (by decide : 124944429 ≤ 124977197) block0 block1

theorem join_0_1 : (twinPrimeSegment 124977197 125042733).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 124977197 ≤ 125009965)
    (by decide : 125009965 ≤ 125042733) block2 block3

theorem join_1_0 : (twinPrimeSegment 124911661 125042733).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 124911661 ≤ 124977197)
    (by decide : 124977197 ≤ 125042733) join_0_0 join_0_1

theorem total : (twinPrimeSegment 124911661 125042733).card = 488 := join_1_0

end S059C09
end Sude.GeneratedTwinScan
