import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101974061 102006829 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101974061 102006829).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101974061 102006829
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102006829 102039597 = 125 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 102006829 102039597).card = 125 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102006829 102039597
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102039597 102072365 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 102039597 102072365).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102039597 102072365
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 102072365 102105133 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 102072365 102105133).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 102072365 102105133
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101974061 102039597).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 101974061 ≤ 102006829)
    (by decide : 102006829 ≤ 102039597) block0 block1

theorem join_0_1 : (twinPrimeSegment 102039597 102105133).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 102039597 ≤ 102072365)
    (by decide : 102072365 ≤ 102105133) block2 block3

theorem join_1_0 : (twinPrimeSegment 101974061 102105133).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 101974061 ≤ 102039597)
    (by decide : 102039597 ≤ 102105133) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101974061 102105133).card = 495 := join_1_0

end S048C10
end Sude.GeneratedTwinScan
