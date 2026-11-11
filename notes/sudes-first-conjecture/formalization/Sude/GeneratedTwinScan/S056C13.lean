import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S056C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119144493 119177261 = 109 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 119144493 119177261).card = 109 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119144493 119177261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119177261 119210029 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 119177261 119210029).card = 105 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119177261 119210029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119210029 119242797 = 127 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 119210029 119242797).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119210029 119242797
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 119242797 119275565 = 154 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 119242797 119275565).card = 154 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 119242797 119275565
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 119144493 119210029).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 119144493 ≤ 119177261)
    (by decide : 119177261 ≤ 119210029) block0 block1

theorem join_0_1 : (twinPrimeSegment 119210029 119275565).card = 281 := by
  simpa using combineTwinPrimeSegments (by decide : 119210029 ≤ 119242797)
    (by decide : 119242797 ≤ 119275565) block2 block3

theorem join_1_0 : (twinPrimeSegment 119144493 119275565).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 119144493 ≤ 119210029)
    (by decide : 119210029 ≤ 119275565) join_0_0 join_0_1

theorem total : (twinPrimeSegment 119144493 119275565).card = 495 := join_1_0

end S056C13
end Sude.GeneratedTwinScan
