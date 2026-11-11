import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S071C08
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149946413 149979181 = 123 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 149946413 149979181).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149946413 149979181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 149979181 150011949 = 135 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 149979181 150011949).card = 135 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 149979181 150011949
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150011949 150044717 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 150011949 150044717).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150011949 150044717
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 150044717 150077485 = 113 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 150044717 150077485).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 150044717 150077485
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 149946413 150011949).card = 258 := by
  simpa using combineTwinPrimeSegments (by decide : 149946413 ≤ 149979181)
    (by decide : 149979181 ≤ 150011949) block0 block1

theorem join_0_1 : (twinPrimeSegment 150011949 150077485).card = 232 := by
  simpa using combineTwinPrimeSegments (by decide : 150011949 ≤ 150044717)
    (by decide : 150044717 ≤ 150077485) block2 block3

theorem join_1_0 : (twinPrimeSegment 149946413 150077485).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 149946413 ≤ 150011949)
    (by decide : 150011949 ≤ 150077485) join_0_0 join_0_1

theorem total : (twinPrimeSegment 149946413 150077485).card = 490 := join_1_0

end S071C08
end Sude.GeneratedTwinScan
