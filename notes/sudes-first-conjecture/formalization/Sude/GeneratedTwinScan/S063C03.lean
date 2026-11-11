import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132513837 132546605 = 126 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 132513837 132546605).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132513837 132546605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132546605 132579373 = 121 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 132546605 132579373).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132546605 132579373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132579373 132612141 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 132579373 132612141).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132579373 132612141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 132612141 132644909 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 132612141 132644909).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 132612141 132644909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 132513837 132579373).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 132513837 ≤ 132546605)
    (by decide : 132546605 ≤ 132579373) block0 block1

theorem join_0_1 : (twinPrimeSegment 132579373 132644909).card = 240 := by
  simpa using combineTwinPrimeSegments (by decide : 132579373 ≤ 132612141)
    (by decide : 132612141 ≤ 132644909) block2 block3

theorem join_1_0 : (twinPrimeSegment 132513837 132644909).card = 487 := by
  simpa using combineTwinPrimeSegments (by decide : 132513837 ≤ 132579373)
    (by decide : 132579373 ≤ 132644909) join_0_0 join_0_1

theorem total : (twinPrimeSegment 132513837 132644909).card = 487 := join_1_0

end S063C03
end Sude.GeneratedTwinScan
