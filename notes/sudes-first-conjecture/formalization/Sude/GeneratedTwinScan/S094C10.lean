import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S094C10
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14088)) 198443053 198475821 = 122 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 198443053 198475821).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14088 198443053 198475821
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14089)) 198475821 198508589 = 126 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 198475821 198508589).card = 126 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14089 198475821 198508589
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14090)) 198508589 198541357 = 122 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 198508589 198541357).card = 122 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14090 198508589 198541357
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14091)) 198541357 198574125 = 120 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 198541357 198574125).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14091 198541357 198574125
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 198443053 198508589).card = 248 := by
  simpa using combineTwinPrimeSegments (by decide : 198443053 ≤ 198475821)
    (by decide : 198475821 ≤ 198508589) block0 block1

theorem join_0_1 : (twinPrimeSegment 198508589 198574125).card = 242 := by
  simpa using combineTwinPrimeSegments (by decide : 198508589 ≤ 198541357)
    (by decide : 198541357 ≤ 198574125) block2 block3

theorem join_1_0 : (twinPrimeSegment 198443053 198574125).card = 490 := by
  simpa using combineTwinPrimeSegments (by decide : 198443053 ≤ 198508589)
    (by decide : 198508589 ≤ 198574125) join_0_0 join_0_1

theorem total : (twinPrimeSegment 198443053 198574125).card = 490 := join_1_0

end S094C10
end Sude.GeneratedTwinScan
