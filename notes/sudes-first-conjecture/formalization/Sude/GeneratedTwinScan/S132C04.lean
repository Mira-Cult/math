import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S132C04
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16654)) 277348397 277381165 = 120 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 277348397 277381165).card = 120 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16654 277348397 277381165
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16655)) 277381165 277413933 = 99 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 277381165 277413933).card = 99 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16655 277381165 277413933
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16656)) 277413933 277446701 = 115 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 277413933 277446701).card = 115 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16656 277413933 277446701
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 16657)) 277446701 277479469 = 112 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 277446701 277479469).card = 112 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 16657 277446701 277479469
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 277348397 277413933).card = 219 := by
  simpa using combineTwinPrimeSegments (by decide : 277348397 ≤ 277381165)
    (by decide : 277381165 ≤ 277413933) block0 block1

theorem join_0_1 : (twinPrimeSegment 277413933 277479469).card = 227 := by
  simpa using combineTwinPrimeSegments (by decide : 277413933 ≤ 277446701)
    (by decide : 277446701 ≤ 277479469) block2 block3

theorem join_1_0 : (twinPrimeSegment 277348397 277479469).card = 446 := by
  simpa using combineTwinPrimeSegments (by decide : 277348397 ≤ 277413933)
    (by decide : 277413933 ≤ 277479469) join_0_0 join_0_1

theorem total : (twinPrimeSegment 277348397 277479469).card = 446 := join_1_0

end S132C04
end Sude.GeneratedTwinScan
