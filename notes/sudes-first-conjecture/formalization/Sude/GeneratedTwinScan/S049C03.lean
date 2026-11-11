import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103153709 103186477 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 103153709 103186477).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103153709 103186477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103186477 103219245 = 115 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 103186477 103219245).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103186477 103219245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103219245 103252013 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 103219245 103252013).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103219245 103252013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 103252013 103284781 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 103252013 103284781).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 103252013 103284781
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 103153709 103219245).card = 234 := by
  simpa using combineTwinPrimeSegments (by decide : 103153709 ≤ 103186477)
    (by decide : 103186477 ≤ 103219245) block0 block1

theorem join_0_1 : (twinPrimeSegment 103219245 103284781).card = 251 := by
  simpa using combineTwinPrimeSegments (by decide : 103219245 ≤ 103252013)
    (by decide : 103252013 ≤ 103284781) block2 block3

theorem join_1_0 : (twinPrimeSegment 103153709 103284781).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 103153709 ≤ 103219245)
    (by decide : 103219245 ≤ 103284781) join_0_0 join_0_1

theorem total : (twinPrimeSegment 103153709 103284781).card = 485 := join_1_0

end S049C03
end Sude.GeneratedTwinScan
