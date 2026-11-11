import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S053C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112328749 112361517 = 140 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 112328749 112361517).card = 140 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112328749 112361517
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112361517 112394285 = 123 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 112361517 112394285).card = 123 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112361517 112394285
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112394285 112427053 = 132 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 112394285 112427053).card = 132 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112394285 112427053
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 112427053 112459821 = 138 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 112427053 112459821).card = 138 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 112427053 112459821
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 112328749 112394285).card = 263 := by
  simpa using combineTwinPrimeSegments (by decide : 112328749 ≤ 112361517)
    (by decide : 112361517 ≤ 112394285) block0 block1

theorem join_0_1 : (twinPrimeSegment 112394285 112459821).card = 270 := by
  simpa using combineTwinPrimeSegments (by decide : 112394285 ≤ 112427053)
    (by decide : 112427053 ≤ 112459821) block2 block3

theorem join_1_0 : (twinPrimeSegment 112328749 112459821).card = 533 := by
  simpa using combineTwinPrimeSegments (by decide : 112328749 ≤ 112394285)
    (by decide : 112394285 ≤ 112459821) join_0_0 join_0_1

theorem total : (twinPrimeSegment 112328749 112459821).card = 533 := join_1_0

end S053C09
end Sude.GeneratedTwinScan
