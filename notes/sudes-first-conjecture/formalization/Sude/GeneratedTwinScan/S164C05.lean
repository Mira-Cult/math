import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S164C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18563)) 344588333 344621101 = 99 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 344588333 344621101).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18563 344588333 344621101
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18564)) 344621101 344653869 = 118 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 344621101 344653869).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18564 344621101 344653869
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18565)) 344653869 344686637 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 344653869 344686637).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18565 344653869 344686637
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18566)) 344686637 344719405 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 344686637 344719405).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18566 344686637 344719405
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 344588333 344653869).card = 217 := by
  simpa using combineTwinPrimeSegments (by decide : 344588333 ≤ 344621101)
    (by decide : 344621101 ≤ 344653869) block0 block1

theorem join_0_1 : (twinPrimeSegment 344653869 344719405).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 344653869 ≤ 344686637)
    (by decide : 344686637 ≤ 344719405) block2 block3

theorem join_1_0 : (twinPrimeSegment 344588333 344719405).card = 445 := by
  simpa using combineTwinPrimeSegments (by decide : 344588333 ≤ 344653869)
    (by decide : 344653869 ≤ 344719405) join_0_0 join_0_1

theorem total : (twinPrimeSegment 344588333 344719405).card = 445 := join_1_0

end S164C05
end Sude.GeneratedTwinScan
