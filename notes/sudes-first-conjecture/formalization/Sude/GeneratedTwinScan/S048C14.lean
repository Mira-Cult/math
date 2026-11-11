import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102498349 102531117 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 102498349 102531117).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102498349 102531117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102531117 102563885 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102531117 102563885).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102531117 102563885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102563885 102596653 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102563885 102596653).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102563885 102596653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102596653 102629421 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102596653 102629421).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102596653 102629421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 102498349 102563885).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 102498349 ≤ 102531117)
    (by decide : 102531117 ≤ 102563885) block0 block1

theorem join_0_1 : (twinPrimeSegment 102563885 102629421).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 102563885 ≤ 102596653)
    (by decide : 102596653 ≤ 102629421) block2 block3

theorem join_1_0 : (twinPrimeSegment 102498349 102629421).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 102498349 ≤ 102563885)
    (by decide : 102563885 ≤ 102629421) join_0_0 join_0_1

theorem total : (twinPrimeSegment 102498349 102629421).card = 504 := join_1_0

end S048C14
end Sude.GeneratedTwinScan
