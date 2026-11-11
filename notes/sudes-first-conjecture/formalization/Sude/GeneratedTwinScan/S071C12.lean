import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150470701 150503469 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150470701 150503469).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150470701 150503469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150503469 150536237 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 150503469 150536237).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150503469 150536237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150536237 150569005 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150536237 150569005).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150536237 150569005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150569005 150601773 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150569005 150601773).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150569005 150601773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150470701 150536237).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 150470701 ≤ 150503469)
    (by decide : 150503469 ≤ 150536237) block0 block1

theorem join_0_1 : (twinPrimeSegment 150536237 150601773).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 150536237 ≤ 150569005)
    (by decide : 150569005 ≤ 150601773) block2 block3

theorem join_1_0 : (twinPrimeSegment 150470701 150601773).card = 489 := by
  simpa using combineTwinPrimeSegments (by decide : 150470701 ≤ 150536237)
    (by decide : 150536237 ≤ 150601773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150470701 150601773).card = 489 := join_1_0

end S071C12
end Sude.GeneratedTwinScan
