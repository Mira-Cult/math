import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S044C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94240813 94273581 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 94240813 94273581).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94240813 94273581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94273581 94306349 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 94273581 94306349).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94273581 94306349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94306349 94339117 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 94306349 94339117).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94306349 94339117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94339117 94371885 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 94339117 94371885).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94339117 94371885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 94240813 94306349).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 94240813 ≤ 94273581)
    (by decide : 94273581 ≤ 94306349) block0 block1

theorem join_0_1 : (twinPrimeSegment 94306349 94371885).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 94306349 ≤ 94339117)
    (by decide : 94339117 ≤ 94371885) block2 block3

theorem join_1_0 : (twinPrimeSegment 94240813 94371885).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 94240813 ≤ 94306349)
    (by decide : 94306349 ≤ 94371885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 94240813 94371885).card = 522 := join_1_0

end S044C15
end Sude.GeneratedTwinScan
