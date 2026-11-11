import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111673389 111706157 = 144 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111673389 111706157).card = 144 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111673389 111706157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111706157 111738925 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111706157 111738925).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111706157 111738925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111738925 111771693 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 111738925 111771693).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111738925 111771693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111771693 111804461 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 111771693 111804461).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111771693 111804461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111673389 111738925).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 111673389 ≤ 111706157)
    (by decide : 111706157 ≤ 111738925) block0 block1

theorem join_0_1 : (twinPrimeSegment 111738925 111804461).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 111738925 ≤ 111771693)
    (by decide : 111771693 ≤ 111804461) block2 block3

theorem join_1_0 : (twinPrimeSegment 111673389 111804461).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 111673389 ≤ 111738925)
    (by decide : 111738925 ≤ 111804461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111673389 111804461).card = 533 := join_1_0

end S053C04
end Sude.GeneratedTwinScan
