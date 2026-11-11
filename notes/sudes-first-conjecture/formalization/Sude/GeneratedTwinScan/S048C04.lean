import Sude.FiniteTwinOddBaseComplete
import Sude.FiniteTwinActive
import Sude.TwinStrideSixCompressed

/-! Generated FT count hints; Lean checks each block. -/
namespace Sude.GeneratedTwinScan
namespace S048C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101187629 101220397 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 101187629 101220397).card = 122 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101187629 101220397
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101220397 101253165 = 117 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 101220397 101253165).card = 117 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101220397 101253165
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101253165 101285933 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 101253165 101285933).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101253165 101285933
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan finiteTwinCheckedBase 101285933 101318701 = 119 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 101285933 101318701).card = 119 := by
  have h := strideSixCompressedIntervalScan_spec finiteTwinCheckedBase 32768 101285933 101318701
    finiteTwinCheckedBase_complete (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 101187629 101253165).card = 239 := by
  simpa using combineTwinPrimeSegments (by decide : 101187629 ≤ 101220397)
    (by decide : 101220397 ≤ 101253165) block0 block1

theorem join_0_1 : (twinPrimeSegment 101253165 101318701).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 101253165 ≤ 101285933)
    (by decide : 101285933 ≤ 101318701) block2 block3

theorem join_1_0 : (twinPrimeSegment 101187629 101318701).card = 477 := by
  simpa using combineTwinPrimeSegments (by decide : 101187629 ≤ 101253165)
    (by decide : 101253165 ≤ 101318701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 101187629 101318701).card = 477 := join_1_0

end S048C04
end Sude.GeneratedTwinScan
