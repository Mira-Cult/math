import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S245C13
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22705)) 515506221 515538989 = 118 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 515506221 515538989).card = 118 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22705 515506221 515538989
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22706)) 515538989 515571757 = 108 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 515538989 515571757).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22706 515538989 515571757
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22706)) 515571757 515604525 = 107 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 515571757 515604525).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22706 515571757 515604525
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22707)) 515604525 515637293 = 93 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 515604525 515637293).card = 93 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22707 515604525 515637293
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 515506221 515571757).card = 226 := by
  simpa using combineTwinPrimeSegments (by decide : 515506221 ≤ 515538989)
    (by decide : 515538989 ≤ 515571757) block0 block1

theorem join_0_1 : (twinPrimeSegment 515571757 515637293).card = 200 := by
  simpa using combineTwinPrimeSegments (by decide : 515571757 ≤ 515604525)
    (by decide : 515604525 ≤ 515637293) block2 block3

theorem join_1_0 : (twinPrimeSegment 515506221 515637293).card = 426 := by
  simpa using combineTwinPrimeSegments (by decide : 515506221 ≤ 515571757)
    (by decide : 515571757 ≤ 515637293) join_0_0 join_0_1

theorem total : (twinPrimeSegment 515506221 515637293).card = 426 := join_1_0

end S245C13
end Sude.GeneratedTwinScan
