import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S043C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92012589 92045357 = 129 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 92012589 92045357).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92012589 92045357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92045357 92078125 = 147 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 92045357 92078125).card = 147 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92045357 92078125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92078125 92110893 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 92078125 92110893).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92078125 92110893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 92110893 92143661 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 92110893 92143661).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 92110893 92143661
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 92012589 92078125).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 92012589 ≤ 92045357)
    (by decide : 92045357 ≤ 92078125) block0 block1

theorem join_0_1 : (twinPrimeSegment 92078125 92143661).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 92078125 ≤ 92110893)
    (by decide : 92110893 ≤ 92143661) block2 block3

theorem join_1_0 : (twinPrimeSegment 92012589 92143661).card = 553 := by
  simpa using combineTwinPrimeSegments (by decide : 92012589 ≤ 92078125)
    (by decide : 92078125 ≤ 92143661) join_0_0 join_0_1

theorem total : (twinPrimeSegment 92012589 92143661).card = 553 := join_1_0

end S043C14
end Sude.GeneratedTwinScan
