import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82706477 82739245 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 82706477 82739245).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82706477 82739245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82739245 82772013 = 131 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 82739245 82772013).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82739245 82772013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82772013 82804781 = 150 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 82772013 82804781).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82772013 82804781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82804781 82837549 = 111 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 82804781 82837549).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82804781 82837549
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 82706477 82772013).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 82706477 ≤ 82739245)
    (by decide : 82739245 ≤ 82772013) block0 block1

theorem join_0_1 : (twinPrimeSegment 82772013 82837549).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 82772013 ≤ 82804781)
    (by decide : 82804781 ≤ 82837549) block2 block3

theorem join_1_0 : (twinPrimeSegment 82706477 82837549).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 82706477 ≤ 82772013)
    (by decide : 82772013 ≤ 82837549) join_0_0 join_0_1

theorem total : (twinPrimeSegment 82706477 82837549).card = 510 := join_1_0

end S039C07
end Sude.GeneratedTwinScan
