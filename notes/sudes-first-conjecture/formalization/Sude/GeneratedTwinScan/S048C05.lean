import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101318701 101351469 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101318701 101351469).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101318701 101351469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101351469 101384237 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 101351469 101384237).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101351469 101384237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101384237 101417005 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 101384237 101417005).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101384237 101417005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101417005 101449773 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101417005 101449773).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101417005 101449773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101318701 101384237).card = 262 := by
  simpa using combineTwinPrimeSegments (by decide : 101318701 ≤ 101351469)
    (by decide : 101351469 ≤ 101384237) block0 block1

theorem join_0_1 : (twinPrimeSegment 101384237 101449773).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 101384237 ≤ 101417005)
    (by decide : 101417005 ≤ 101449773) block2 block3

theorem join_1_0 : (twinPrimeSegment 101318701 101449773).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 101318701 ≤ 101384237)
    (by decide : 101384237 ≤ 101449773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101318701 101449773).card = 517 := join_1_0

end S048C05
end Sude.GeneratedTwinScan
