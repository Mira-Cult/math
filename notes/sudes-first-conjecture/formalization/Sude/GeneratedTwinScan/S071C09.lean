import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150077485 150110253 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 150077485 150110253).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150077485 150110253
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150110253 150143021 = 114 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 150110253 150143021).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150110253 150143021
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150143021 150175789 = 126 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150143021 150175789).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150143021 150175789
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150175789 150208557 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150175789 150208557).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150175789 150208557
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 150077485 150143021).card = 241 := by
  simpa using combineTwinPrimeSegments (by decide : 150077485 ≤ 150110253)
    (by decide : 150110253 ≤ 150143021) block0 block1

theorem join_0_1 : (twinPrimeSegment 150143021 150208557).card = 254 := by
  simpa using combineTwinPrimeSegments (by decide : 150143021 ≤ 150175789)
    (by decide : 150175789 ≤ 150208557) block2 block3

theorem join_1_0 : (twinPrimeSegment 150077485 150208557).card = 495 := by
  simpa using combineTwinPrimeSegments (by decide : 150077485 ≤ 150143021)
    (by decide : 150143021 ≤ 150208557) join_0_0 join_0_1

theorem total : (twinPrimeSegment 150077485 150208557).card = 495 := join_1_0

end S071C09
end Sude.GeneratedTwinScan
