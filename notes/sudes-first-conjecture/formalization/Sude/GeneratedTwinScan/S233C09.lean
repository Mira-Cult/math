import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S233C09
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22132)) 489816109 489848877 = 108 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 489816109 489848877).card = 108 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22132 489816109 489848877
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22133)) 489848877 489881645 = 113 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 489848877 489881645).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22133 489848877 489881645
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22134)) 489881645 489914413 = 114 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 489881645 489914413).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22134 489881645 489914413
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22134)) 489914413 489947181 = 130 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 489914413 489947181).card = 130 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22134 489914413 489947181
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 489816109 489881645).card = 221 := by
  simpa using combineTwinPrimeSegments (by decide : 489816109 ≤ 489848877)
    (by decide : 489848877 ≤ 489881645) block0 block1

theorem join_0_1 : (twinPrimeSegment 489881645 489947181).card = 244 := by
  simpa using combineTwinPrimeSegments (by decide : 489881645 ≤ 489914413)
    (by decide : 489914413 ≤ 489947181) block2 block3

theorem join_1_0 : (twinPrimeSegment 489816109 489947181).card = 465 := by
  simpa using combineTwinPrimeSegments (by decide : 489816109 ≤ 489881645)
    (by decide : 489881645 ≤ 489947181) join_0_0 join_0_1

theorem total : (twinPrimeSegment 489816109 489947181).card = 465 := join_1_0

end S233C09
end Sude.GeneratedTwinScan
