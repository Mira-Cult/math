import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105250861 105283629 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 105250861 105283629).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105250861 105283629
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105283629 105316397 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105283629 105316397).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105283629 105316397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105316397 105349165 = 133 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105316397 105349165).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105316397 105349165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105349165 105381933 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 105349165 105381933).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105349165 105381933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 105250861 105316397).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 105250861 ≤ 105283629)
    (by decide : 105283629 ≤ 105316397) block0 block1

theorem join_0_1 : (twinPrimeSegment 105316397 105381933).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 105316397 ≤ 105349165)
    (by decide : 105349165 ≤ 105381933) block2 block3

theorem join_1_0 : (twinPrimeSegment 105250861 105381933).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 105250861 ≤ 105316397)
    (by decide : 105316397 ≤ 105381933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 105250861 105381933).card = 511 := join_1_0

end S050C03
end Sude.GeneratedTwinScan
