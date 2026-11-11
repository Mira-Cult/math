import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S035C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75104301 75137069 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 75104301 75137069).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75104301 75137069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75137069 75169837 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 75137069 75169837).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75137069 75169837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75169837 75202605 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 75169837 75202605).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75169837 75202605
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 75202605 75235373 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 75202605 75235373).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 75202605 75235373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 75104301 75169837).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 75104301 ≤ 75137069)
    (by decide : 75137069 ≤ 75169837) block0 block1

theorem join_0_1 : (twinPrimeSegment 75169837 75235373).card = 271 := by
  simpa using combineTwinPrimeSegments (by decide : 75169837 ≤ 75202605)
    (by decide : 75202605 ≤ 75235373) block2 block3

theorem join_1_0 : (twinPrimeSegment 75104301 75235373).card = 519 := by
  simpa using combineTwinPrimeSegments (by decide : 75104301 ≤ 75169837)
    (by decide : 75169837 ≤ 75235373) join_0_0 join_0_1

theorem total : (twinPrimeSegment 75104301 75235373).card = 519 := join_1_0

end S035C13
end Sude.GeneratedTwinScan
