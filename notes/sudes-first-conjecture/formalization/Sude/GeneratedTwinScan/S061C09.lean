import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129105965 129138733 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 129105965 129138733).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129105965 129138733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129138733 129171501 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 129138733 129171501).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129138733 129171501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129171501 129204269 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 129171501 129204269).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129171501 129204269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 129204269 129237037 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 129204269 129237037).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 129204269 129237037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 129105965 129171501).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 129105965 ≤ 129138733)
    (by decide : 129138733 ≤ 129171501) block0 block1

theorem join_0_1 : (twinPrimeSegment 129171501 129237037).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 129171501 ≤ 129204269)
    (by decide : 129204269 ≤ 129237037) block2 block3

theorem join_1_0 : (twinPrimeSegment 129105965 129237037).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 129105965 ≤ 129171501)
    (by decide : 129171501 ≤ 129237037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 129105965 129237037).card = 514 := join_1_0

end S061C09
end Sude.GeneratedTwinScan
