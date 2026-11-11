import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105381933 105414701 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 105381933 105414701).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105381933 105414701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105414701 105447469 = 134 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 105414701 105447469).card = 134 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105414701 105447469
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105447469 105480237 = 136 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 105447469 105480237).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105447469 105480237
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 105480237 105513005 = 121 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 105480237 105513005).card = 121 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 105480237 105513005
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 105381933 105447469).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 105381933 ≤ 105414701)
    (by decide : 105414701 ≤ 105447469) block0 block1

theorem join_0_1 : (twinPrimeSegment 105447469 105513005).card = 257 := by
  simpa using combineTwinPrimeSegments (by decide : 105447469 ≤ 105480237)
    (by decide : 105480237 ≤ 105513005) block2 block3

theorem join_1_0 : (twinPrimeSegment 105381933 105513005).card = 511 := by
  simpa using combineTwinPrimeSegments (by decide : 105381933 ≤ 105447469)
    (by decide : 105447469 ≤ 105513005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 105381933 105513005).card = 511 := join_1_0

end S050C04
end Sude.GeneratedTwinScan
