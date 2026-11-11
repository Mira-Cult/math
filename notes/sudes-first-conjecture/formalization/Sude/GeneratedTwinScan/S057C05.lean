import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120193069 120225837 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120193069 120225837).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120193069 120225837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120225837 120258605 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 120225837 120258605).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120225837 120258605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120258605 120291373 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 120258605 120291373).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120258605 120291373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120291373 120324141 = 109 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120291373 120324141).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120291373 120324141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120193069 120258605).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 120193069 ≤ 120225837)
    (by decide : 120225837 ≤ 120258605) block0 block1

theorem join_0_1 : (twinPrimeSegment 120258605 120324141).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 120258605 ≤ 120291373)
    (by decide : 120291373 ≤ 120324141) block2 block3

theorem join_1_0 : (twinPrimeSegment 120193069 120324141).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 120193069 ≤ 120258605)
    (by decide : 120258605 ≤ 120324141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120193069 120324141).card = 498 := join_1_0

end S057C05
end Sude.GeneratedTwinScan
