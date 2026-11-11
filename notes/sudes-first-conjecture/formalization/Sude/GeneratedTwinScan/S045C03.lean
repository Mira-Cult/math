import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S045C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94765101 94797869 = 125 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 94765101 94797869).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94765101 94797869
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94797869 94830637 = 139 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 94797869 94830637).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94797869 94830637
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94830637 94863405 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 94830637 94863405).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94830637 94863405
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 94863405 94896173 = 139 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 94863405 94896173).card = 139 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 94863405 94896173
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 94765101 94830637).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 94765101 ≤ 94797869)
    (by decide : 94797869 ≤ 94830637) block0 block1

theorem join_0_1 : (twinPrimeSegment 94830637 94896173).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 94830637 ≤ 94863405)
    (by decide : 94863405 ≤ 94896173) block2 block3

theorem join_1_0 : (twinPrimeSegment 94765101 94896173).card = 538 := by
  simpa using combineTwinPrimeSegments (by decide : 94765101 ≤ 94830637)
    (by decide : 94830637 ≤ 94896173) join_0_0 join_0_1

theorem total : (twinPrimeSegment 94765101 94896173).card = 538 := join_1_0

end S045C03
end Sude.GeneratedTwinScan
