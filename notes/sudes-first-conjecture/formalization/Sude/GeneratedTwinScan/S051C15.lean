import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S051C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108920877 108953645 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 108920877 108953645).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108920877 108953645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108953645 108986413 = 127 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 108953645 108986413).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108953645 108986413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 108986413 109019181 = 123 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 108986413 109019181).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 108986413 109019181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 109019181 109051949 = 142 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 109019181 109051949).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 109019181 109051949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 108920877 108986413).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 108920877 ≤ 108953645)
    (by decide : 108953645 ≤ 108986413) block0 block1

theorem join_0_1 : (twinPrimeSegment 108986413 109051949).card = 265 := by
  simpa using combineTwinPrimeSegments (by decide : 108986413 ≤ 109019181)
    (by decide : 109019181 ≤ 109051949) block2 block3

theorem join_1_0 : (twinPrimeSegment 108920877 109051949).card = 520 := by
  simpa using combineTwinPrimeSegments (by decide : 108920877 ≤ 108986413)
    (by decide : 108986413 ≤ 109051949) join_0_0 join_0_1

theorem total : (twinPrimeSegment 108920877 109051949).card = 520 := join_1_0

end S051C15
end Sude.GeneratedTwinScan
