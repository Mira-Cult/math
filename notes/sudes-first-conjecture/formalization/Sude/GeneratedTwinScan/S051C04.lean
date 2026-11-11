import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107479085 107511853 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 107479085 107511853).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107479085 107511853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107511853 107544621 = 122 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 107511853 107544621).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107511853 107544621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107544621 107577389 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 107544621 107577389).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107544621 107577389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 107577389 107610157 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 107577389 107610157).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 107577389 107610157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 107479085 107544621).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 107479085 ≤ 107511853)
    (by decide : 107511853 ≤ 107544621) block0 block1

theorem join_0_1 : (twinPrimeSegment 107544621 107610157).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 107544621 ≤ 107577389)
    (by decide : 107577389 ≤ 107610157) block2 block3

theorem join_1_0 : (twinPrimeSegment 107479085 107610157).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 107479085 ≤ 107544621)
    (by decide : 107544621 ≤ 107610157) join_0_0 join_0_1

theorem total : (twinPrimeSegment 107479085 107610157).card = 514 := join_1_0

end S051C04
end Sude.GeneratedTwinScan
