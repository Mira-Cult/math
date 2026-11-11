import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S042C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89522221 89554989 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 89522221 89554989).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89522221 89554989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89554989 89587757 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 89554989 89587757).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89554989 89587757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89587757 89620525 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 89587757 89620525).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89587757 89620525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 89620525 89653293 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 89620525 89653293).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 89620525 89653293
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 89522221 89587757).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 89522221 ≤ 89554989)
    (by decide : 89554989 ≤ 89587757) block0 block1

theorem join_0_1 : (twinPrimeSegment 89587757 89653293).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 89587757 ≤ 89620525)
    (by decide : 89620525 ≤ 89653293) block2 block3

theorem join_1_0 : (twinPrimeSegment 89522221 89653293).card = 468 := by
  simpa using combineTwinPrimeSegments (by decide : 89522221 ≤ 89587757)
    (by decide : 89587757 ≤ 89653293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 89522221 89653293).card = 468 := join_1_0

end S042C11
end Sude.GeneratedTwinScan
