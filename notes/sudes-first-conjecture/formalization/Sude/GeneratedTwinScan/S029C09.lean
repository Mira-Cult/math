import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 61997101 62029869 = 145 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 61997101 62029869).card = 145 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 61997101 62029869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62029869 62062637 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62029869 62062637).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62029869 62062637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62062637 62095405 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62062637 62095405).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62062637 62095405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62095405 62128173 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 62095405 62128173).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62095405 62128173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 61997101 62062637).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 61997101 ≤ 62029869)
    (by decide : 62029869 ≤ 62062637) block0 block1

theorem join_0_1 : (twinPrimeSegment 62062637 62128173).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 62062637 ≤ 62095405)
    (by decide : 62095405 ≤ 62128173) block2 block3

theorem join_1_0 : (twinPrimeSegment 61997101 62128173).card = 528 := by
  simpa using combineTwinPrimeSegments (by decide : 61997101 ≤ 62062637)
    (by decide : 62062637 ≤ 62128173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 61997101 62128173).card = 528 := join_1_0

end S029C09
end Sude.GeneratedTwinScan
