import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72876077 72908845 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 72876077 72908845).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72876077 72908845
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72908845 72941613 = 146 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 72908845 72941613).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72908845 72941613
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72941613 72974381 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72941613 72974381).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72941613 72974381
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72974381 73007149 = 132 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72974381 73007149).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72974381 73007149
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 72876077 72941613).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 72876077 ≤ 72908845)
    (by decide : 72908845 ≤ 72941613) block0 block1

theorem join_0_1 : (twinPrimeSegment 72941613 73007149).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 72941613 ≤ 72974381)
    (by decide : 72974381 ≤ 73007149) block2 block3

theorem join_1_0 : (twinPrimeSegment 72876077 73007149).card = 532 := by
  simpa using combineTwinPrimeSegments (by decide : 72876077 ≤ 72941613)
    (by decide : 72941613 ≤ 73007149) join_0_0 join_0_1

theorem total : (twinPrimeSegment 72876077 73007149).card = 532 := join_1_0

end S034C12
end Sude.GeneratedTwinScan
