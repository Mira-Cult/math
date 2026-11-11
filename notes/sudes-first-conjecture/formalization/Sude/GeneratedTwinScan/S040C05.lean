import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S040C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84541485 84574253 = 124 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 84541485 84574253).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84541485 84574253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84574253 84607021 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 84574253 84607021).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84574253 84607021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84607021 84639789 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 84607021 84639789).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84607021 84639789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 84639789 84672557 = 136 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 84639789 84672557).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 84639789 84672557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 84541485 84607021).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 84541485 ≤ 84574253)
    (by decide : 84574253 ≤ 84607021) block0 block1

theorem join_0_1 : (twinPrimeSegment 84607021 84672557).card = 264 := by
  simpa using combineTwinPrimeSegments (by decide : 84607021 ≤ 84639789)
    (by decide : 84639789 ≤ 84672557) block2 block3

theorem join_1_0 : (twinPrimeSegment 84541485 84672557).card = 514 := by
  simpa using combineTwinPrimeSegments (by decide : 84541485 ≤ 84607021)
    (by decide : 84607021 ≤ 84672557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 84541485 84672557).card = 514 := join_1_0

end S040C05
end Sude.GeneratedTwinScan
