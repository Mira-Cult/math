import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112984109 113016877 = 132 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 112984109 113016877).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112984109 113016877
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113016877 113049645 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 113016877 113049645).card = 113 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113016877 113049645
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113049645 113082413 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 113049645 113082413).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113049645 113082413
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 113082413 113115181 = 117 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 113082413 113115181).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 113082413 113115181
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 112984109 113049645).card = 245 := by
  simpa using combineTwinPrimeSegments (by decide : 112984109 ≤ 113016877)
    (by decide : 113016877 ≤ 113049645) block0 block1

theorem join_0_1 : (twinPrimeSegment 113049645 113115181).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 113049645 ≤ 113082413)
    (by decide : 113082413 ≤ 113115181) block2 block3

theorem join_1_0 : (twinPrimeSegment 112984109 113115181).card = 484 := by
  simpa using combineTwinPrimeSegments (by decide : 112984109 ≤ 113049645)
    (by decide : 113049645 ≤ 113115181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 112984109 113115181).card = 484 := join_1_0

end S053C14
end Sude.GeneratedTwinScan
