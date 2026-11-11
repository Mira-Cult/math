import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C01
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128057389 128090157 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128057389 128090157).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128057389 128090157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128090157 128122925 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 128090157 128122925).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128090157 128122925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128122925 128155693 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 128122925 128155693).card = 112 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128122925 128155693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128155693 128188461 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128155693 128188461).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128155693 128188461
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128057389 128122925).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 128057389 ≤ 128090157)
    (by decide : 128090157 ≤ 128122925) block0 block1

theorem join_0_1 : (twinPrimeSegment 128122925 128188461).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 128122925 ≤ 128155693)
    (by decide : 128155693 ≤ 128188461) block2 block3

theorem join_1_0 : (twinPrimeSegment 128057389 128188461).card = 482 := by
  simpa using combineTwinPrimeSegments (by decide : 128057389 ≤ 128122925)
    (by decide : 128122925 ≤ 128188461) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128057389 128188461).card = 482 := join_1_0

end S061C01
end Sude.GeneratedTwinScan
