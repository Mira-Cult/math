import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95551533 95584301 = 119 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 95551533 95584301).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95551533 95584301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95584301 95617069 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 95584301 95617069).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95584301 95617069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95617069 95649837 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 95617069 95649837).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95617069 95649837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 95649837 95682605 = 141 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 95649837 95682605).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 95649837 95682605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 95551533 95617069).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 95551533 ≤ 95584301)
    (by decide : 95584301 ≤ 95617069) block0 block1

theorem join_0_1 : (twinPrimeSegment 95617069 95682605).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 95617069 ≤ 95649837)
    (by decide : 95649837 ≤ 95682605) block2 block3

theorem join_1_0 : (twinPrimeSegment 95551533 95682605).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 95551533 ≤ 95617069)
    (by decide : 95617069 ≤ 95682605) join_0_0 join_0_1

theorem total : (twinPrimeSegment 95551533 95682605).card = 490 := join_1_0

end S045C09
end Sude.GeneratedTwinScan
