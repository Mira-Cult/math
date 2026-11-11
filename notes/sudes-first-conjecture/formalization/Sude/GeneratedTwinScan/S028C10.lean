import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60031021 60063789 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 60031021 60063789).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60031021 60063789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60063789 60096557 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 60063789 60096557).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60063789 60096557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60096557 60129325 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 60096557 60129325).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60096557 60129325
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60129325 60162093 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 60129325 60162093).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60129325 60162093
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 60031021 60096557).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 60031021 ≤ 60063789)
    (by decide : 60063789 ≤ 60096557) block0 block1

theorem join_0_1 : (twinPrimeSegment 60096557 60162093).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 60096557 ≤ 60129325)
    (by decide : 60129325 ≤ 60162093) block2 block3

theorem join_1_0 : (twinPrimeSegment 60031021 60162093).card = 512 := by
  simpa using combineTwinPrimeSegments (by decide : 60031021 ≤ 60096557)
    (by decide : 60096557 ≤ 60162093) join_0_0 join_0_1

theorem total : (twinPrimeSegment 60031021 60162093).card = 512 := join_1_0

end S028C10
end Sude.GeneratedTwinScan
