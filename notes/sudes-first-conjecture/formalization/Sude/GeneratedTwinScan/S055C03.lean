import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S055C03
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115736621 115769389 = 127 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 115736621 115769389).card = 127 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115736621 115769389
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115769389 115802157 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 115769389 115802157).card = 126 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115769389 115802157
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115802157 115834925 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 115802157 115834925).card = 114 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115802157 115834925
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 115834925 115867693 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 115834925 115867693).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 115834925 115867693
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 115736621 115802157).card = 253 := by
  simpa using combineTwinPrimeSegments (by decide : 115736621 ≤ 115769389)
    (by decide : 115769389 ≤ 115802157) block0 block1

theorem join_0_1 : (twinPrimeSegment 115802157 115867693).card = 249 := by
  simpa using combineTwinPrimeSegments (by decide : 115802157 ≤ 115834925)
    (by decide : 115834925 ≤ 115867693) block2 block3

theorem join_1_0 : (twinPrimeSegment 115736621 115867693).card = 502 := by
  simpa using combineTwinPrimeSegments (by decide : 115736621 ≤ 115802157)
    (by decide : 115802157 ≤ 115867693) join_0_0 join_0_1

theorem total : (twinPrimeSegment 115736621 115867693).card = 502 := join_1_0

end S055C03
end Sude.GeneratedTwinScan
