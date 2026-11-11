import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S159C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18293)) 334626861 334659629 = 112 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 334626861 334659629).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18293 334626861 334659629
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18294)) 334659629 334692397 = 101 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 334659629 334692397).card = 101 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18294 334659629 334692397
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18295)) 334692397 334725165 = 110 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 334692397 334725165).card = 110 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18295 334692397 334725165
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 18296)) 334725165 334757933 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 334725165 334757933).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 18296 334725165 334757933
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 334626861 334692397).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 334626861 ≤ 334659629)
    (by decide : 334659629 ≤ 334692397) block0 block1

theorem join_0_1 : (twinPrimeSegment 334692397 334757933).card = 222 := by
  simpa using combineTwinPrimeSegments (by decide : 334692397 ≤ 334725165)
    (by decide : 334725165 ≤ 334757933) block2 block3

theorem join_1_0 : (twinPrimeSegment 334626861 334757933).card = 435 := by
  simpa using combineTwinPrimeSegments (by decide : 334626861 ≤ 334692397)
    (by decide : 334692397 ≤ 334757933) join_0_0 join_0_1

theorem total : (twinPrimeSegment 334626861 334757933).card = 435 := join_1_0

end S159C09
end Sude.GeneratedTwinScan
