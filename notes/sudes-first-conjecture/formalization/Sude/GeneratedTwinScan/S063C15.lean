import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S063C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134086701 134119469 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 134086701 134119469).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134086701 134119469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134119469 134152237 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 134119469 134152237).card = 101 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134119469 134152237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134152237 134185005 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 134152237 134185005).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134152237 134185005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 134185005 134217773 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 134185005 134217773).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 134185005 134217773
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 134086701 134152237).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 134086701 ≤ 134119469)
    (by decide : 134119469 ≤ 134152237) block0 block1

theorem join_0_1 : (twinPrimeSegment 134152237 134217773).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 134152237 ≤ 134185005)
    (by decide : 134185005 ≤ 134217773) block2 block3

theorem join_1_0 : (twinPrimeSegment 134086701 134217773).card = 472 := by
  simpa using combineTwinPrimeSegments (by decide : 134086701 ≤ 134152237)
    (by decide : 134152237 ≤ 134217773) join_0_0 join_0_1

theorem total : (twinPrimeSegment 134086701 134217773).card = 472 := join_1_0

end S063C15
end Sude.GeneratedTwinScan
