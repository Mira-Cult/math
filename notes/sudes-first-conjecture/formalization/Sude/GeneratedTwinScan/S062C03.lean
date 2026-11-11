import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S062C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130416685 130449453 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 130416685 130449453).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130416685 130449453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130449453 130482221 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 130449453 130482221).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130449453 130482221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130482221 130514989 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 130482221 130514989).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130482221 130514989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 130514989 130547757 = 107 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 130514989 130547757).card = 107 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 130514989 130547757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 130416685 130482221).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 130416685 ≤ 130449453)
    (by decide : 130449453 ≤ 130482221) block0 block1

theorem join_0_1 : (twinPrimeSegment 130482221 130547757).card = 236 := by
  simpa using combineTwinPrimeSegments (by decide : 130482221 ≤ 130514989)
    (by decide : 130514989 ≤ 130547757) block2 block3

theorem join_1_0 : (twinPrimeSegment 130416685 130547757).card = 483 := by
  simpa using combineTwinPrimeSegments (by decide : 130416685 ≤ 130482221)
    (by decide : 130482221 ≤ 130547757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 130416685 130547757).card = 483 := join_1_0

end S062C03
end Sude.GeneratedTwinScan
