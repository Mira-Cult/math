import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127139885 127172653 = 115 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127139885 127172653).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127139885 127172653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127172653 127205421 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127172653 127205421).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127172653 127205421
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127205421 127238189 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127205421 127238189).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127205421 127238189
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127238189 127270957 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 127238189 127270957).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127238189 127270957
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127139885 127205421).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 127139885 ≤ 127172653)
    (by decide : 127172653 ≤ 127205421) block0 block1

theorem join_0_1 : (twinPrimeSegment 127205421 127270957).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 127205421 ≤ 127238189)
    (by decide : 127238189 ≤ 127270957) block2 block3

theorem join_1_0 : (twinPrimeSegment 127139885 127270957).card = 504 := by
  simpa using combineTwinPrimeSegments (by decide : 127139885 ≤ 127205421)
    (by decide : 127205421 ≤ 127270957) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127139885 127270957).card = 504 := join_1_0

end S060C10
end Sude.GeneratedTwinScan
