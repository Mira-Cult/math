import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82051117 82083885 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 82051117 82083885).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82051117 82083885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82083885 82116653 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 82083885 82116653).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82083885 82116653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82116653 82149421 = 148 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 82116653 82149421).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82116653 82149421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 82149421 82182189 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 82149421 82182189).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 82149421 82182189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 82051117 82116653).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 82051117 ≤ 82083885)
    (by decide : 82083885 ≤ 82116653) block0 block1

theorem join_0_1 : (twinPrimeSegment 82116653 82182189).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 82116653 ≤ 82149421)
    (by decide : 82149421 ≤ 82182189) block2 block3

theorem join_1_0 : (twinPrimeSegment 82051117 82182189).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 82051117 ≤ 82116653)
    (by decide : 82116653 ≤ 82182189) join_0_0 join_0_1

theorem total : (twinPrimeSegment 82051117 82182189).card = 529 := join_1_0

end S039C02
end Sude.GeneratedTwinScan
