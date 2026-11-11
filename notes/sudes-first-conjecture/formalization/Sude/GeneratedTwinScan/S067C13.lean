import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S067C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142213165 142245933 = 114 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 142213165 142245933).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142213165 142245933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142245933 142278701 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 142245933 142278701).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142245933 142278701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142278701 142311469 = 108 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 142278701 142311469).card = 108 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142278701 142311469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 142311469 142344237 = 110 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 142311469 142344237).card = 110 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 142311469 142344237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 142213165 142278701).card = 223 := by
  simpa using combineTwinPrimeSegments (by decide : 142213165 ≤ 142245933)
    (by decide : 142245933 ≤ 142278701) block0 block1

theorem join_0_1 : (twinPrimeSegment 142278701 142344237).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 142278701 ≤ 142311469)
    (by decide : 142311469 ≤ 142344237) block2 block3

theorem join_1_0 : (twinPrimeSegment 142213165 142344237).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 142213165 ≤ 142278701)
    (by decide : 142278701 ≤ 142344237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 142213165 142344237).card = 441 := join_1_0

end S067C13
end Sude.GeneratedTwinScan
