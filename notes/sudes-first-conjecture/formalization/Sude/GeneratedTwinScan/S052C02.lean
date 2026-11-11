import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109314093 109346861 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109314093 109346861).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109314093 109346861
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109346861 109379629 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 109346861 109379629).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109346861 109379629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109379629 109412397 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 109379629 109412397).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109379629 109412397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109412397 109445165 = 148 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109412397 109445165).card = 148 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109412397 109445165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109314093 109379629).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 109314093 ≤ 109346861)
    (by decide : 109346861 ≤ 109379629) block0 block1

theorem join_0_1 : (twinPrimeSegment 109379629 109445165).card = 282 := by
  simpa using combineTwinPrimeSegments (by decide : 109379629 ≤ 109412397)
    (by decide : 109412397 ≤ 109445165) block2 block3

theorem join_1_0 : (twinPrimeSegment 109314093 109445165).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 109314093 ≤ 109379629)
    (by decide : 109379629 ≤ 109445165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109314093 109445165).card = 539 := join_1_0

end S052C02
end Sude.GeneratedTwinScan
