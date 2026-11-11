import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149815341 149848109 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149815341 149848109).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149815341 149848109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149848109 149880877 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149848109 149880877).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149848109 149880877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149880877 149913645 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 149880877 149913645).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149880877 149913645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149913645 149946413 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 149913645 149946413).card = 99 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149913645 149946413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149815341 149880877).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 149815341 ≤ 149848109)
    (by decide : 149848109 ≤ 149880877) block0 block1

theorem join_0_1 : (twinPrimeSegment 149880877 149946413).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 149880877 ≤ 149913645)
    (by decide : 149913645 ≤ 149946413) block2 block3

theorem join_1_0 : (twinPrimeSegment 149815341 149946413).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 149815341 ≤ 149880877)
    (by decide : 149880877 ≤ 149946413) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149815341 149946413).card = 444 := join_1_0

end S071C07
end Sude.GeneratedTwinScan
