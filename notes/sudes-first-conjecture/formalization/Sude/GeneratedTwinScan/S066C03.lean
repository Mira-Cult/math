import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S066C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138805293 138838061 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 138805293 138838061).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138805293 138838061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138838061 138870829 = 156 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 138838061 138870829).card = 156 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138838061 138870829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138870829 138903597 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 138870829 138903597).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138870829 138903597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 138903597 138936365 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 138903597 138936365).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 138903597 138936365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 138805293 138870829).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 138805293 ≤ 138838061)
    (by decide : 138838061 ≤ 138870829) block0 block1

theorem join_0_1 : (twinPrimeSegment 138870829 138936365).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 138870829 ≤ 138903597)
    (by decide : 138903597 ≤ 138936365) block2 block3

theorem join_1_0 : (twinPrimeSegment 138805293 138936365).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 138805293 ≤ 138870829)
    (by decide : 138870829 ≤ 138936365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 138805293 138936365).card = 514 := join_1_0

end S066C03
end Sude.GeneratedTwinScan
