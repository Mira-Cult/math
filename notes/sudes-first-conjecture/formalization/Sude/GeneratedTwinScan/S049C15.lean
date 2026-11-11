import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S049C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104726573 104759341 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 104726573 104759341).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104726573 104759341
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104759341 104792109 = 132 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 104759341 104792109).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104759341 104792109
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104792109 104824877 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 104792109 104824877).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104792109 104824877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 104824877 104857645 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 104824877 104857645).card = 130 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 104824877 104857645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 104726573 104792109).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 104726573 ≤ 104759341)
    (by decide : 104759341 ≤ 104792109) block0 block1

theorem join_0_1 : (twinPrimeSegment 104792109 104857645).card = 250 := by
  simpa using combineTwinPrimeSegments (by decide : 104792109 ≤ 104824877)
    (by decide : 104824877 ≤ 104857645) block2 block3

theorem join_1_0 : (twinPrimeSegment 104726573 104857645).card = 510 := by
  simpa using combineTwinPrimeSegments (by decide : 104726573 ≤ 104792109)
    (by decide : 104792109 ≤ 104857645) join_0_0 join_0_1

theorem total : (twinPrimeSegment 104726573 104857645).card = 510 := join_1_0

end S049C15
end Sude.GeneratedTwinScan
