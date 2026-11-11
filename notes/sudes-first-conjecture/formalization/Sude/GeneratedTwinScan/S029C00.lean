import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60817453 60850221 = 147 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 60817453 60850221).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60817453 60850221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60850221 60882989 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 60850221 60882989).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60850221 60882989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60882989 60915757 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 60882989 60915757).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60882989 60915757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60915757 60948525 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 60915757 60948525).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60915757 60948525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 60817453 60882989).card = 286 := by
  simpa using combineTwinPrimeSegments (by decide : 60817453 ≤ 60850221)
    (by decide : 60850221 ≤ 60882989) block0 block1

theorem join_0_1 : (twinPrimeSegment 60882989 60948525).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 60882989 ≤ 60915757)
    (by decide : 60915757 ≤ 60948525) block2 block3

theorem join_1_0 : (twinPrimeSegment 60817453 60948525).card = 550 := by
  simpa using combineTwinPrimeSegments (by decide : 60817453 ≤ 60882989)
    (by decide : 60882989 ≤ 60948525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 60817453 60948525).card = 550 := join_1_0

end S029C00
end Sude.GeneratedTwinScan
