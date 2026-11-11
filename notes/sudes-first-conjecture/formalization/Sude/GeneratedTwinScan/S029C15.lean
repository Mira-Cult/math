import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S029C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62783533 62816301 = 137 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 62783533 62816301).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62783533 62816301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62816301 62849069 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62816301 62849069).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62816301 62849069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62849069 62881837 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62849069 62881837).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62849069 62881837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62881837 62914605 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 62881837 62914605).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62881837 62914605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 62783533 62849069).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 62783533 ≤ 62816301)
    (by decide : 62816301 ≤ 62849069) block0 block1

theorem join_0_1 : (twinPrimeSegment 62849069 62914605).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 62849069 ≤ 62881837)
    (by decide : 62881837 ≤ 62914605) block2 block3

theorem join_1_0 : (twinPrimeSegment 62783533 62914605).card = 527 := by
  simpa using combineTwinPrimeSegments (by decide : 62783533 ≤ 62849069)
    (by decide : 62849069 ≤ 62914605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 62783533 62914605).card = 527 := join_1_0

end S029C15
end Sude.GeneratedTwinScan
