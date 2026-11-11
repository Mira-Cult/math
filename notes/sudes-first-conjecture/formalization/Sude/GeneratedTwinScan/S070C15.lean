import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S070C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148766765 148799533 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 148766765 148799533).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148766765 148799533
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148799533 148832301 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 148799533 148832301).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148799533 148832301
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148832301 148865069 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 148832301 148865069).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148832301 148865069
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 148865069 148897837 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 148865069 148897837).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 148865069 148897837
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 148766765 148832301).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 148766765 ≤ 148799533)
    (by decide : 148799533 ≤ 148832301) block0 block1

theorem join_0_1 : (twinPrimeSegment 148832301 148897837).card = 246 := by
  simpa using combineTwinPrimeSegments (by decide : 148832301 ≤ 148865069)
    (by decide : 148865069 ≤ 148897837) block2 block3

theorem join_1_0 : (twinPrimeSegment 148766765 148897837).card = 485 := by
  simpa using combineTwinPrimeSegments (by decide : 148766765 ≤ 148832301)
    (by decide : 148832301 ≤ 148897837) join_0_0 join_0_1

theorem total : (twinPrimeSegment 148766765 148897837).card = 485 := join_1_0

end S070C15
end Sude.GeneratedTwinScan
