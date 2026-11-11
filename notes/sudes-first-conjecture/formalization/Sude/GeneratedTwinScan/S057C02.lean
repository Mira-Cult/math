import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119799853 119832621 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 119799853 119832621).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119799853 119832621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119832621 119865389 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 119832621 119865389).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119832621 119865389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119865389 119898157 = 118 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 119865389 119898157).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119865389 119898157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119898157 119930925 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 119898157 119930925).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119898157 119930925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 119799853 119865389).card = 256 := by
  simpa using combineTwinPrimeSegments (by decide : 119799853 ≤ 119832621)
    (by decide : 119832621 ≤ 119865389) block0 block1

theorem join_0_1 : (twinPrimeSegment 119865389 119930925).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 119865389 ≤ 119898157)
    (by decide : 119898157 ≤ 119930925) block2 block3

theorem join_1_0 : (twinPrimeSegment 119799853 119930925).card = 494 := by
  simpa using combineTwinPrimeSegments (by decide : 119799853 ≤ 119865389)
    (by decide : 119865389 ≤ 119930925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 119799853 119930925).card = 494 := join_1_0

end S057C02
end Sude.GeneratedTwinScan
