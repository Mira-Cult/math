import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S050C11
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106299437 106332205 = 150 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 106299437 106332205).card = 150 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106299437 106332205
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106332205 106364973 = 119 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 106332205 106364973).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106332205 106364973
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106364973 106397741 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 106364973 106397741).card = 129 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106364973 106397741
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 106397741 106430509 = 131 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 106397741 106430509).card = 131 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 106397741 106430509
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 106299437 106364973).card = 269 := by
  simpa using combineTwinPrimeSegments (by decide : 106299437 ≤ 106332205)
    (by decide : 106332205 ≤ 106364973) block0 block1

theorem join_0_1 : (twinPrimeSegment 106364973 106430509).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 106364973 ≤ 106397741)
    (by decide : 106397741 ≤ 106430509) block2 block3

theorem join_1_0 : (twinPrimeSegment 106299437 106430509).card = 529 := by
  simpa using combineTwinPrimeSegments (by decide : 106299437 ≤ 106364973)
    (by decide : 106364973 ≤ 106430509) join_0_0 join_0_1

theorem total : (twinPrimeSegment 106299437 106430509).card = 529 := join_1_0

end S050C11
end Sude.GeneratedTwinScan
