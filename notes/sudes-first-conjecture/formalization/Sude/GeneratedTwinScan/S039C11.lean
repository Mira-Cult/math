import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S039C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83230765 83263533 = 160 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 83230765 83263533).card = 160 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83230765 83263533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83263533 83296301 = 140 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 83263533 83296301).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83263533 83296301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83296301 83329069 = 139 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 83296301 83329069).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83296301 83329069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 83329069 83361837 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 83329069 83361837).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 83329069 83361837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 83230765 83296301).card = 300 := by
  simpa using combineTwinPrimeSegments (by decide : 83230765 ≤ 83263533)
    (by decide : 83263533 ≤ 83296301) block0 block1

theorem join_0_1 : (twinPrimeSegment 83296301 83361837).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 83296301 ≤ 83329069)
    (by decide : 83329069 ≤ 83361837) block2 block3

theorem join_1_0 : (twinPrimeSegment 83230765 83361837).card = 560 := by
  simpa using combineTwinPrimeSegments (by decide : 83230765 ≤ 83296301)
    (by decide : 83296301 ≤ 83361837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 83230765 83361837).card = 560 := join_1_0

end S039C11
end Sude.GeneratedTwinScan
