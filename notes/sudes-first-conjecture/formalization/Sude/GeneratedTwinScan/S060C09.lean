import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127008813 127041581 = 135 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127008813 127041581).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127008813 127041581
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127041581 127074349 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127041581 127074349).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127041581 127074349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127074349 127107117 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127074349 127107117).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127074349 127107117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127107117 127139885 = 124 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 127107117 127139885).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127107117 127139885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127008813 127074349).card = 276 := by
  simpa using combineTwinPrimeSegments (by decide : 127008813 ≤ 127041581)
    (by decide : 127041581 ≤ 127074349) block0 block1

theorem join_0_1 : (twinPrimeSegment 127074349 127139885).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 127074349 ≤ 127107117)
    (by decide : 127107117 ≤ 127139885) block2 block3

theorem join_1_0 : (twinPrimeSegment 127008813 127139885).card = 524 := by
  simpa using combineTwinPrimeSegments (by decide : 127008813 ≤ 127074349)
    (by decide : 127074349 ≤ 127139885) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127008813 127139885).card = 524 := join_1_0

end S060C09
end Sude.GeneratedTwinScan
