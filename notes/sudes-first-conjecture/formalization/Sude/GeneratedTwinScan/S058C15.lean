import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S058C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123600941 123633709 = 138 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 123600941 123633709).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123600941 123633709
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123633709 123666477 = 137 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 123633709 123666477).card = 137 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123633709 123666477
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123666477 123699245 = 124 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 123666477 123699245).card = 124 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123666477 123699245
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 123699245 123732013 = 135 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 123699245 123732013).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 123699245 123732013
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 123600941 123666477).card = 275 := by
  simpa using combineTwinPrimeSegments (by decide : 123600941 ≤ 123633709)
    (by decide : 123633709 ≤ 123666477) block0 block1

theorem join_0_1 : (twinPrimeSegment 123666477 123732013).card = 259 := by
  simpa using combineTwinPrimeSegments (by decide : 123666477 ≤ 123699245)
    (by decide : 123699245 ≤ 123732013) block2 block3

theorem join_1_0 : (twinPrimeSegment 123600941 123732013).card = 534 := by
  simpa using combineTwinPrimeSegments (by decide : 123600941 ≤ 123666477)
    (by decide : 123666477 ≤ 123732013) join_0_0 join_0_1

theorem total : (twinPrimeSegment 123600941 123732013).card = 534 := join_1_0

end S058C15
end Sude.GeneratedTwinScan
