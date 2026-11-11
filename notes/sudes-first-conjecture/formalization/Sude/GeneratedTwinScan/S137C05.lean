import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S137C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16970)) 287965229 287997997 = 110 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 287965229 287997997).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16970 287965229 287997997
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16971)) 287997997 288030765 = 128 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 287997997 288030765).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16971 287997997 288030765
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16972)) 288030765 288063533 = 121 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 288030765 288063533).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16972 288030765 288063533
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16973)) 288063533 288096301 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 288063533 288096301).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16973 288063533 288096301
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 287965229 288030765).card = 238 := by
  simpa using combineTwinPrimeSegments (by decide : 287965229 ≤ 287997997)
    (by decide : 287997997 ≤ 288030765) block0 block1

theorem join_0_1 : (twinPrimeSegment 288030765 288096301).card = 237 := by
  simpa using combineTwinPrimeSegments (by decide : 288030765 ≤ 288063533)
    (by decide : 288063533 ≤ 288096301) block2 block3

theorem join_1_0 : (twinPrimeSegment 287965229 288096301).card = 475 := by
  simpa using combineTwinPrimeSegments (by decide : 287965229 ≤ 288030765)
    (by decide : 288030765 ≤ 288096301) join_0_0 join_0_1

theorem total : (twinPrimeSegment 287965229 288096301).card = 475 := join_1_0

end S137C05
end Sude.GeneratedTwinScan
