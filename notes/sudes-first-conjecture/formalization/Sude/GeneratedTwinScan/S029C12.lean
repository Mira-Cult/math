import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62390317 62423085 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 62390317 62423085).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62390317 62423085
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62423085 62455853 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62423085 62455853).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62423085 62455853
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62455853 62488621 = 138 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62455853 62488621).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62455853 62488621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62488621 62521389 = 108 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 62488621 62521389).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62488621 62521389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 62390317 62455853).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 62390317 ≤ 62423085)
    (by decide : 62423085 ≤ 62455853) block0 block1

theorem join_0_1 : (twinPrimeSegment 62455853 62521389).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 62455853 ≤ 62488621)
    (by decide : 62488621 ≤ 62521389) block2 block3

theorem join_1_0 : (twinPrimeSegment 62390317 62521389).card = 501 := by
  simpa using combineTwinPrimeSegments (by decide : 62390317 ≤ 62455853)
    (by decide : 62455853 ≤ 62521389) join_0_0 join_0_1

theorem total : (twinPrimeSegment 62390317 62521389).card = 501 := join_1_0

end S029C12
end Sude.GeneratedTwinScan
