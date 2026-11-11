import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111542317 111575085 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 111542317 111575085).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111542317 111575085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111575085 111607853 = 130 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 111575085 111607853).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111575085 111607853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111607853 111640621 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 111607853 111640621).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111607853 111640621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 111640621 111673389 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 111640621 111673389).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 111640621 111673389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 111542317 111607853).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 111542317 ≤ 111575085)
    (by decide : 111575085 ≤ 111607853) block0 block1

theorem join_0_1 : (twinPrimeSegment 111607853 111673389).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 111607853 ≤ 111640621)
    (by decide : 111640621 ≤ 111673389) block2 block3

theorem join_1_0 : (twinPrimeSegment 111542317 111673389).card = 505 := by
  simpa using combineTwinPrimeSegments (by decide : 111542317 ≤ 111607853)
    (by decide : 111607853 ≤ 111673389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 111542317 111673389).card = 505 := join_1_0

end S053C03
end Sude.GeneratedTwinScan
