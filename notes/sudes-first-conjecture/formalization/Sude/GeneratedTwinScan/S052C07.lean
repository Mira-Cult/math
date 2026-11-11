import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S052C07
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109969453 110002221 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 109969453 110002221).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109969453 110002221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110002221 110034989 = 129 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 110002221 110034989).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110002221 110034989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110034989 110067757 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 110034989 110067757).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110034989 110067757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 110067757 110100525 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 110067757 110100525).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 110067757 110100525
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 109969453 110034989).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 109969453 ≤ 110002221)
    (by decide : 110002221 ≤ 110034989) block0 block1

theorem join_0_1 : (twinPrimeSegment 110034989 110100525).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 110034989 ≤ 110067757)
    (by decide : 110067757 ≤ 110100525) block2 block3

theorem join_1_0 : (twinPrimeSegment 109969453 110100525).card = 488 := by
  simpa using combineTwinPrimeSegments (by decide : 109969453 ≤ 110034989)
    (by decide : 110034989 ≤ 110100525) join_0_0 join_0_1

theorem total : (twinPrimeSegment 109969453 110100525).card = 488 := join_1_0

end S052C07
end Sude.GeneratedTwinScan
