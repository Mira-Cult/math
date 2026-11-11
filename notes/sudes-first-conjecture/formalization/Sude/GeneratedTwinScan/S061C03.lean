import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S061C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128319533 128352301 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 128319533 128352301).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128319533 128352301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128352301 128385069 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 128352301 128385069).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128352301 128385069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128385069 128417837 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 128385069 128417837).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128385069 128417837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 128417837 128450605 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 128417837 128450605).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 128417837 128450605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 128319533 128385069).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 128319533 ≤ 128352301)
    (by decide : 128352301 ≤ 128385069) block0 block1

theorem join_0_1 : (twinPrimeSegment 128385069 128450605).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 128385069 ≤ 128417837)
    (by decide : 128417837 ≤ 128450605) block2 block3

theorem join_1_0 : (twinPrimeSegment 128319533 128450605).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 128319533 ≤ 128385069)
    (by decide : 128385069 ≤ 128450605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 128319533 128450605).card = 504 := join_1_0

end S061C03
end Sude.GeneratedTwinScan
