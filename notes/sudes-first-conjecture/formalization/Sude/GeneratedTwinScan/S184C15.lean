import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S184C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19694)) 387842093 387874861 = 113 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 387842093 387874861).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19694 387842093 387874861
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19695)) 387874861 387907629 = 98 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 387874861 387907629).card = 98 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19695 387874861 387907629
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19696)) 387907629 387940397 = 128 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 387907629 387940397).card = 128 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19696 387907629 387940397
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 19697)) 387940397 387973165 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 387940397 387973165).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 19697 387940397 387973165
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 387842093 387907629).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 387842093 ≤ 387874861)
    (by decide : 387874861 ≤ 387907629) block0 block1

theorem join_0_1 : (twinPrimeSegment 387907629 387973165).card = 228 := by
  simpa using combineTwinPrimeSegments (by decide : 387907629 ≤ 387940397)
    (by decide : 387940397 ≤ 387973165) block2 block3

theorem join_1_0 : (twinPrimeSegment 387842093 387973165).card = 439 := by
  simpa using combineTwinPrimeSegments (by decide : 387842093 ≤ 387907629)
    (by decide : 387907629 ≤ 387973165) join_0_0 join_0_1

theorem total : (twinPrimeSegment 387842093 387973165).card = 439 := join_1_0

end S184C15
end Sude.GeneratedTwinScan
