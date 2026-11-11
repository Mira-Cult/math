import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64880685 64913453 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 64880685 64913453).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64880685 64913453
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64913453 64946221 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 64913453 64946221).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64913453 64946221
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64946221 64978989 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 64946221 64978989).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64946221 64978989
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 64978989 65011757 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 64978989 65011757).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 64978989 65011757
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 64880685 64946221).card = 266 := by
  simpa using combineTwinPrimeSegments (by decide : 64880685 ≤ 64913453)
    (by decide : 64913453 ≤ 64946221) block0 block1

theorem join_0_1 : (twinPrimeSegment 64946221 65011757).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 64946221 ≤ 64978989)
    (by decide : 64978989 ≤ 65011757) block2 block3

theorem join_1_0 : (twinPrimeSegment 64880685 65011757).card = 523 := by
  simpa using combineTwinPrimeSegments (by decide : 64880685 ≤ 64946221)
    (by decide : 64946221 ≤ 65011757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 64880685 65011757).card = 523 := join_1_0

end S030C15
end Sude.GeneratedTwinScan
