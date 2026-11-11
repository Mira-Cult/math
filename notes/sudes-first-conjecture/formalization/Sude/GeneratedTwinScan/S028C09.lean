import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59899949 59932717 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 59899949 59932717).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59899949 59932717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59932717 59965485 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 59932717 59965485).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59932717 59965485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59965485 59998253 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 59965485 59998253).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59965485 59998253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 59998253 60031021 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 59998253 60031021).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 59998253 60031021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 59899949 59965485).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 59899949 ≤ 59932717)
    (by decide : 59932717 ≤ 59965485) block0 block1

theorem join_0_1 : (twinPrimeSegment 59965485 60031021).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 59965485 ≤ 59998253)
    (by decide : 59998253 ≤ 60031021) block2 block3

theorem join_1_0 : (twinPrimeSegment 59899949 60031021).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 59899949 ≤ 59965485)
    (by decide : 59965485 ≤ 60031021) join_0_0 join_0_1

theorem total : (twinPrimeSegment 59899949 60031021).card = 533 := join_1_0

end S028C09
end Sude.GeneratedTwinScan
