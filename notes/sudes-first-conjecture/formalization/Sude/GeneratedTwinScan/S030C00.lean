import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S030C00
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62914605 62947373 = 154 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 62914605 62947373).card = 154 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62914605 62947373
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62947373 62980141 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 62947373 62980141).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62947373 62980141
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 62980141 63012909 = 140 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 62980141 63012909).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 62980141 63012909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 63012909 63045677 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 63012909 63045677).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 63012909 63045677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 62914605 62980141).card = 280 := by
  simpa using combineTwinPrimeSegments (by decide : 62914605 ≤ 62947373)
    (by decide : 62947373 ≤ 62980141) block0 block1

theorem join_0_1 : (twinPrimeSegment 62980141 63045677).card = 277 := by
  simpa using combineTwinPrimeSegments (by decide : 62980141 ≤ 63012909)
    (by decide : 63012909 ≤ 63045677) block2 block3

theorem join_1_0 : (twinPrimeSegment 62914605 63045677).card = 557 := by
  simpa using combineTwinPrimeSegments (by decide : 62914605 ≤ 62980141)
    (by decide : 62980141 ≤ 63045677) join_0_0 join_0_1

theorem total : (twinPrimeSegment 62914605 63045677).card = 557 := join_1_0

end S030C00
end Sude.GeneratedTwinScan
