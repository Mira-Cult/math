import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S143C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17333)) 300417069 300449837 = 121 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 300417069 300449837).card = 121 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17333 300417069 300449837
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17334)) 300449837 300482605 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 300449837 300482605).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17334 300449837 300482605
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17335)) 300482605 300515373 = 119 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 300482605 300515373).card = 119 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17335 300482605 300515373
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 17336)) 300515373 300548141 = 99 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 300515373 300548141).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 17336 300515373 300548141
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 300417069 300482605).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 300417069 ≤ 300449837)
    (by decide : 300449837 ≤ 300482605) block0 block1

theorem join_0_1 : (twinPrimeSegment 300482605 300548141).card = 218 := by
  simpa using combineTwinPrimeSegments (by decide : 300482605 ≤ 300515373)
    (by decide : 300515373 ≤ 300548141) block2 block3

theorem join_1_0 : (twinPrimeSegment 300417069 300548141).card = 444 := by
  simpa using combineTwinPrimeSegments (by decide : 300417069 ≤ 300482605)
    (by decide : 300482605 ≤ 300548141) join_0_0 join_0_1

theorem total : (twinPrimeSegment 300417069 300548141).card = 444 := join_1_0

end S143C04
end Sude.GeneratedTwinScan
