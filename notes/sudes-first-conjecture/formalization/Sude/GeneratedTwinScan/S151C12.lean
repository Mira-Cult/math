import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S151C12
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17840)) 318242861 318275629 = 105 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 318242861 318275629).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17840 318242861 318275629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17841)) 318275629 318308397 = 124 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 318275629 318308397).card = 124 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17841 318275629 318308397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17842)) 318308397 318341165 = 111 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 318308397 318341165).card = 111 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17842 318308397 318341165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17843)) 318341165 318373933 = 127 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 318341165 318373933).card = 127 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17843 318341165 318373933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 318242861 318308397).card = 229 := by
  simpa using combineTwinPrimeSegments (by decide : 318242861 ≤ 318275629)
    (by decide : 318275629 ≤ 318308397) block0 block1

theorem join_0_1 : (twinPrimeSegment 318308397 318373933).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 318308397 ≤ 318341165)
    (by decide : 318341165 ≤ 318373933) block2 block3

theorem join_1_0 : (twinPrimeSegment 318242861 318373933).card = 467 := by
  simpa using combineTwinPrimeSegments (by decide : 318242861 ≤ 318308397)
    (by decide : 318308397 ≤ 318373933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 318242861 318373933).card = 467 := join_1_0

end S151C12
end Sude.GeneratedTwinScan
