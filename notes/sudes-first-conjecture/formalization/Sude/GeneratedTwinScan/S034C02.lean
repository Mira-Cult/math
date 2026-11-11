import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71565357 71598125 = 148 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71565357 71598125).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71565357 71598125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71598125 71630893 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71598125 71630893).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71598125 71630893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71630893 71663661 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 71630893 71663661).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71630893 71663661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71663661 71696429 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71663661 71696429).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71663661 71696429
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71565357 71630893).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 71565357 ≤ 71598125)
    (by decide : 71598125 ≤ 71630893) block0 block1

theorem join_0_1 : (twinPrimeSegment 71630893 71696429).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 71630893 ≤ 71663661)
    (by decide : 71663661 ≤ 71696429) block2 block3

theorem join_1_0 : (twinPrimeSegment 71565357 71696429).card = 532 := by
  simpa using combineTwinPrimeSegments (by decide : 71565357 ≤ 71630893)
    (by decide : 71630893 ≤ 71696429) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71565357 71696429).card = 532 := join_1_0

end S034C02
end Sude.GeneratedTwinScan
