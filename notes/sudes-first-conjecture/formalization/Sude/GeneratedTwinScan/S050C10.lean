import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106168365 106201133 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106168365 106201133).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106168365 106201133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106201133 106233901 = 104 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106201133 106233901).card = 104 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106201133 106233901
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106233901 106266669 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 106233901 106266669).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106233901 106266669
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106266669 106299437 = 143 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106266669 106299437).card = 143 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106266669 106299437
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106168365 106233901).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 106168365 ≤ 106201133)
    (by decide : 106201133 ≤ 106233901) block0 block1

theorem join_0_1 : (twinPrimeSegment 106233901 106299437).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 106233901 ≤ 106266669)
    (by decide : 106266669 ≤ 106299437) block2 block3

theorem join_1_0 : (twinPrimeSegment 106168365 106299437).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 106168365 ≤ 106233901)
    (by decide : 106233901 ≤ 106299437) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106168365 106299437).card = 502 := join_1_0

end S050C10
end Sude.GeneratedTwinScan
