import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S028C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60293165 60325933 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 60293165 60325933).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60293165 60325933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60325933 60358701 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 60325933 60358701).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60325933 60358701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60358701 60391469 = 134 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 60358701 60391469).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60358701 60391469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 60391469 60424237 = 151 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 60391469 60424237).card = 151 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 60391469 60424237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 60293165 60358701).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 60293165 ≤ 60325933)
    (by decide : 60325933 ≤ 60358701) block0 block1

theorem join_0_1 : (twinPrimeSegment 60358701 60424237).card = 285 := by
  simpa using combineTwinPrimeSegments (by decide : 60358701 ≤ 60391469)
    (by decide : 60391469 ≤ 60424237) block2 block3

theorem join_1_0 : (twinPrimeSegment 60293165 60424237).card = 540 := by
  simpa using combineTwinPrimeSegments (by decide : 60293165 ≤ 60358701)
    (by decide : 60358701 ≤ 60424237) join_0_0 join_0_1

theorem total : (twinPrimeSegment 60293165 60424237).card = 540 := join_1_0

end S028C12
end Sude.GeneratedTwinScan
