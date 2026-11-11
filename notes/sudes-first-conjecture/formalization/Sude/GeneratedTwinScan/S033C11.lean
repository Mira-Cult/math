import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70647853 70680621 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 70647853 70680621).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70647853 70680621
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70680621 70713389 = 141 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 70680621 70713389).card = 141 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70680621 70713389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70713389 70746157 = 116 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 70713389 70746157).card = 116 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70713389 70746157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 70746157 70778925 = 123 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 70746157 70778925).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 70746157 70778925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 70647853 70713389).card = 283 := by
  simpa using combineTwinPrimeSegments (by decide : 70647853 ≤ 70680621)
    (by decide : 70680621 ≤ 70713389) block0 block1

theorem join_0_1 : (twinPrimeSegment 70713389 70778925).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 70713389 ≤ 70746157)
    (by decide : 70746157 ≤ 70778925) block2 block3

theorem join_1_0 : (twinPrimeSegment 70647853 70778925).card = 522 := by
  simpa using combineTwinPrimeSegments (by decide : 70647853 ≤ 70713389)
    (by decide : 70713389 ≤ 70778925) join_0_0 join_0_1

theorem total : (twinPrimeSegment 70647853 70778925).card = 522 := join_1_0

end S033C11
end Sude.GeneratedTwinScan
