import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S060C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127270957 127303725 = 117 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 127270957 127303725).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127270957 127303725
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127303725 127336493 = 111 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 127303725 127336493).card = 111 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127303725 127336493
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127336493 127369261 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 127336493 127369261).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127336493 127369261
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 127369261 127402029 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 127369261 127402029).card = 115 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 127369261 127402029
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 127270957 127336493).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 127270957 ≤ 127303725)
    (by decide : 127303725 ≤ 127336493) block0 block1

theorem join_0_1 : (twinPrimeSegment 127336493 127402029).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 127336493 ≤ 127369261)
    (by decide : 127369261 ≤ 127402029) block2 block3

theorem join_1_0 : (twinPrimeSegment 127270957 127402029).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 127270957 ≤ 127336493)
    (by decide : 127336493 ≤ 127402029) join_0_0 join_0_1

theorem total : (twinPrimeSegment 127270957 127402029).card = 465 := join_1_0

end S060C11
end Sude.GeneratedTwinScan
