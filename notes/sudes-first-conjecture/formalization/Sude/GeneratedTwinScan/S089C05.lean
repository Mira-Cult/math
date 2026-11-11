import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S089C05
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13687)) 187301933 187334701 = 131 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 187301933 187334701).card = 131 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13687 187301933 187334701
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13688)) 187334701 187367469 = 116 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 187334701 187367469).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13688 187334701 187367469
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13689)) 187367469 187400237 = 137 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 187367469 187400237).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13689 187367469 187400237
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 13690)) 187400237 187433005 = 137 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 187400237 187433005).card = 137 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 13690 187400237 187433005
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 187301933 187367469).card = 247 := by
  simpa using combineTwinPrimeSegments (by decide : 187301933 ≤ 187334701)
    (by decide : 187334701 ≤ 187367469) block0 block1

theorem join_0_1 : (twinPrimeSegment 187367469 187433005).card = 274 := by
  simpa using combineTwinPrimeSegments (by decide : 187367469 ≤ 187400237)
    (by decide : 187400237 ≤ 187433005) block2 block3

theorem join_1_0 : (twinPrimeSegment 187301933 187433005).card = 521 := by
  simpa using combineTwinPrimeSegments (by decide : 187301933 ≤ 187367469)
    (by decide : 187367469 ≤ 187433005) join_0_0 join_0_1

theorem total : (twinPrimeSegment 187301933 187433005).card = 521 := join_1_0

end S089C05
end Sude.GeneratedTwinScan
