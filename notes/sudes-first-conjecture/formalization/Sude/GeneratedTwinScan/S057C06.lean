import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S057C06
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120324141 120356909 = 142 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 120324141 120356909).card = 142 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120324141 120356909
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120356909 120389677 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 120356909 120389677).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120356909 120389677
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120389677 120422445 = 120 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 120389677 120422445).card = 120 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120389677 120422445
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 120422445 120455213 = 140 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 120422445 120455213).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 120422445 120455213
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 120324141 120389677).card = 255 := by
  simpa using combineTwinPrimeSegments (by decide : 120324141 ≤ 120356909)
    (by decide : 120356909 ≤ 120389677) block0 block1

theorem join_0_1 : (twinPrimeSegment 120389677 120455213).card = 260 := by
  simpa using combineTwinPrimeSegments (by decide : 120389677 ≤ 120422445)
    (by decide : 120422445 ≤ 120455213) block2 block3

theorem join_1_0 : (twinPrimeSegment 120324141 120455213).card = 515 := by
  simpa using combineTwinPrimeSegments (by decide : 120324141 ≤ 120389677)
    (by decide : 120389677 ≤ 120455213) join_0_0 join_0_1

theorem total : (twinPrimeSegment 120324141 120455213).card = 515 := join_1_0

end S057C06
end Sude.GeneratedTwinScan
