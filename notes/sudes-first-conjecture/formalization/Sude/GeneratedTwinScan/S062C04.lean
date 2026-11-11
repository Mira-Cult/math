import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130547757 130580525 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130547757 130580525).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130547757 130580525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130580525 130613293 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130580525 130613293).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130580525 130613293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130613293 130646061 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 130613293 130646061).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130613293 130646061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130646061 130678829 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 130646061 130678829).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130646061 130678829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130547757 130613293).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 130547757 ≤ 130580525)
    (by decide : 130580525 ≤ 130613293) block0 block1

theorem join_0_1 : (twinPrimeSegment 130613293 130678829).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 130613293 ≤ 130646061)
    (by decide : 130646061 ≤ 130678829) block2 block3

theorem join_1_0 : (twinPrimeSegment 130547757 130678829).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 130547757 ≤ 130613293)
    (by decide : 130613293 ≤ 130678829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130547757 130678829).card = 490 := join_1_0

end S062C04
end Sude.GeneratedTwinScan
