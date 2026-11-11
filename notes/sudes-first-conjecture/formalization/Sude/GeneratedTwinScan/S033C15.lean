import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S033C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71172141 71204909 = 128 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 71172141 71204909).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71172141 71204909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71204909 71237677 = 142 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 71204909 71237677).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71204909 71237677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71237677 71270445 = 146 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 71237677 71270445).card = 146 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71237677 71270445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 71270445 71303213 = 128 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 71270445 71303213).card = 128 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 71270445 71303213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 71172141 71237677).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 71172141 ≤ 71204909)
    (by decide : 71204909 ≤ 71237677) block0 block1

theorem join_0_1 : (twinPrimeSegment 71237677 71303213).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 71237677 ≤ 71270445)
    (by decide : 71270445 ≤ 71303213) block2 block3

theorem join_1_0 : (twinPrimeSegment 71172141 71303213).card = 544 := by
  simpa using combineTwinPrimeSegments (by decide : 71172141 ≤ 71237677)
    (by decide : 71237677 ≤ 71303213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 71172141 71303213).card = 544 := join_1_0

end S033C15
end Sude.GeneratedTwinScan
