import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145489965 145522733 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 145489965 145522733).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145489965 145522733
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145522733 145555501 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 145522733 145555501).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145522733 145555501
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145555501 145588269 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145555501 145588269).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145555501 145588269
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145588269 145621037 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145588269 145621037).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145588269 145621037
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 145489965 145555501).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 145489965 ≤ 145522733)
    (by decide : 145522733 ≤ 145555501) block0 block1

theorem join_0_1 : (twinPrimeSegment 145555501 145621037).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 145555501 ≤ 145588269)
    (by decide : 145588269 ≤ 145621037) block2 block3

theorem join_1_0 : (twinPrimeSegment 145489965 145621037).card = 491 := by
  simpa using combineTwinPrimeSegments (by decide : 145489965 ≤ 145555501)
    (by decide : 145555501 ≤ 145621037) join_0_0 join_0_1

theorem total : (twinPrimeSegment 145489965 145621037).card = 491 := join_1_0

end S069C06
end Sude.GeneratedTwinScan
