import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S214C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21197)) 449314861 449347629 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 449314861 449347629).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21197 449314861 449347629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21198)) 449347629 449380397 = 106 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 449347629 449380397).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21198 449347629 449380397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21199)) 449380397 449413165 = 112 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 449380397 449413165).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21199 449380397 449413165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21200)) 449413165 449445933 = 115 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 449413165 449445933).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21200 449413165 449445933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 449314861 449380397).card = 214 := by
  simpa using combineTwinPrimeSegments (by decide : 449314861 ≤ 449347629)
    (by decide : 449347629 ≤ 449380397) block0 block1

theorem join_0_1 : (twinPrimeSegment 449380397 449445933).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 449380397 ≤ 449413165)
    (by decide : 449413165 ≤ 449445933) block2 block3

theorem join_1_0 : (twinPrimeSegment 449314861 449445933).card = 441 := by
  simpa using combineTwinPrimeSegments (by decide : 449314861 ≤ 449380397)
    (by decide : 449380397 ≤ 449445933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 449314861 449445933).card = 441 := join_1_0

end S214C04
end Sude.GeneratedTwinScan
