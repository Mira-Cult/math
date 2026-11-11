import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S069C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145227821 145260589 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 145227821 145260589).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145227821 145260589
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145260589 145293357 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 145260589 145293357).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145260589 145293357
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145293357 145326125 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 145293357 145326125).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145293357 145326125
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 145326125 145358893 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 145326125 145358893).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 145326125 145358893
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 145227821 145293357).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 145227821 ≤ 145260589)
    (by decide : 145260589 ≤ 145293357) block0 block1

theorem join_0_1 : (twinPrimeSegment 145293357 145358893).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 145293357 ≤ 145326125)
    (by decide : 145326125 ≤ 145358893) block2 block3

theorem join_1_0 : (twinPrimeSegment 145227821 145358893).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 145227821 ≤ 145293357)
    (by decide : 145293357 ≤ 145358893) join_0_0 join_0_1

theorem total : (twinPrimeSegment 145227821 145358893).card = 477 := join_1_0

end S069C04
end Sude.GeneratedTwinScan
