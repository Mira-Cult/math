import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S072C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152961069 152993837 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 152961069 152993837).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152961069 152993837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 152993837 153026605 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 152993837 153026605).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 152993837 153026605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 153026605 153059373 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 153026605 153059373).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 153026605 153059373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 153059373 153092141 = 125 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 153059373 153092141).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 153059373 153092141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 152961069 153026605).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 152961069 ≤ 152993837)
    (by decide : 152993837 ≤ 153026605) block0 block1

theorem join_0_1 : (twinPrimeSegment 153026605 153092141).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 153026605 ≤ 153059373)
    (by decide : 153059373 ≤ 153092141) block2 block3

theorem join_1_0 : (twinPrimeSegment 152961069 153092141).card = 498 := by
  simpa using combineTwinPrimeSegments (by decide : 152961069 ≤ 153026605)
    (by decide : 153026605 ≤ 153092141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 152961069 153092141).card = 498 := join_1_0

end S072C15
end Sude.GeneratedTwinScan
