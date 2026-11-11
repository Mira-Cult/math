import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106561581 106594349 = 136 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106561581 106594349).card = 136 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106561581 106594349
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106594349 106627117 = 133 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106594349 106627117).card = 133 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106594349 106627117
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106627117 106659885 = 130 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 106627117 106659885).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106627117 106659885
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106659885 106692653 = 118 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106659885 106692653).card = 118 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106659885 106692653
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106561581 106627117).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 106561581 ≤ 106594349)
    (by decide : 106594349 ≤ 106627117) block0 block1

theorem join_0_1 : (twinPrimeSegment 106627117 106692653).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 106627117 ≤ 106659885)
    (by decide : 106659885 ≤ 106692653) block2 block3

theorem join_1_0 : (twinPrimeSegment 106561581 106692653).card = 517 := by
  simpa using combineTwinPrimeSegments (by decide : 106561581 ≤ 106627117)
    (by decide : 106627117 ≤ 106692653) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106561581 106692653).card = 517 := join_1_0

end S050C13
end Sude.GeneratedTwinScan
