import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S031C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65011757 65044525 = 146 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 65011757 65044525).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65011757 65044525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65044525 65077293 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 65044525 65077293).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65044525 65077293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65077293 65110061 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 65077293 65110061).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65077293 65110061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 65110061 65142829 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 65110061 65142829).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 65110061 65142829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 65011757 65077293).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 65011757 ≤ 65044525)
    (by decide : 65044525 ≤ 65077293) block0 block1

theorem join_0_1 : (twinPrimeSegment 65077293 65142829).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 65077293 ≤ 65110061)
    (by decide : 65110061 ≤ 65142829) block2 block3

theorem join_1_0 : (twinPrimeSegment 65011757 65142829).card = 525 := by
  simpa using combineTwinPrimeSegments (by decide : 65011757 ≤ 65077293)
    (by decide : 65077293 ≤ 65142829) join_0_0 join_0_1

theorem total : (twinPrimeSegment 65011757 65142829).card = 525 := join_1_0

end S031C00
end Sude.GeneratedTwinScan
