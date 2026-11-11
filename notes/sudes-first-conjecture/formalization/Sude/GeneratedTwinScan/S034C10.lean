import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S034C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72613933 72646701 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 72613933 72646701).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72613933 72646701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72646701 72679469 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 72646701 72679469).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72646701 72679469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72679469 72712237 = 135 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 72679469 72712237).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72679469 72712237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 72712237 72745005 = 126 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 72712237 72745005).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 72712237 72745005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 72613933 72679469).card = 278 := by
  simpa using combineTwinPrimeSegments (by decide : 72613933 ≤ 72646701)
    (by decide : 72646701 ≤ 72679469) block0 block1

theorem join_0_1 : (twinPrimeSegment 72679469 72745005).card = 261 := by
  simpa using combineTwinPrimeSegments (by decide : 72679469 ≤ 72712237)
    (by decide : 72712237 ≤ 72745005) block2 block3

theorem join_1_0 : (twinPrimeSegment 72613933 72745005).card = 539 := by
  simpa using combineTwinPrimeSegments (by decide : 72613933 ≤ 72679469)
    (by decide : 72679469 ≤ 72745005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 72613933 72745005).card = 539 := join_1_0

end S034C10
end Sude.GeneratedTwinScan
