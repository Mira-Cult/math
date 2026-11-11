import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73269293 73302061 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 73269293 73302061).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73269293 73302061
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73302061 73334829 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 73302061 73334829).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73302061 73334829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73334829 73367597 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 73334829 73367597).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73334829 73367597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 73367597 73400365 = 133 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 73367597 73400365).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 73367597 73400365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 73269293 73334829).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 73269293 ≤ 73302061)
    (by decide : 73302061 ≤ 73334829) block0 block1

theorem join_0_1 : (twinPrimeSegment 73334829 73400365).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 73334829 ≤ 73367597)
    (by decide : 73367597 ≤ 73400365) block2 block3

theorem join_1_0 : (twinPrimeSegment 73269293 73400365).card = 499 := by
  simpa using combineTwinPrimeSegments (by decide : 73269293 ≤ 73334829)
    (by decide : 73334829 ≤ 73400365) join_0_0 join_0_1

theorem total : (twinPrimeSegment 73269293 73400365).card = 499 := join_1_0

end S034C15
end Sude.GeneratedTwinScan
