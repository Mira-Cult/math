import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S102C15
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14693)) 215875629 215908397 = 106 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 215875629 215908397).card = 106 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14693 215875629 215908397
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14694)) 215908397 215941165 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 215908397 215941165).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14694 215908397 215941165
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14696)) 215941165 215973933 = 129 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 215941165 215973933).card = 129 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14696 215941165 215973933
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 14697)) 215973933 216006701 = 114 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 215973933 216006701).card = 114 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 14697 215973933 216006701
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 215875629 215941165).card = 211 := by
  simpa using combineTwinPrimeSegments (by decide : 215875629 ≤ 215908397)
    (by decide : 215908397 ≤ 215941165) block0 block1

theorem join_0_1 : (twinPrimeSegment 215941165 216006701).card = 243 := by
  simpa using combineTwinPrimeSegments (by decide : 215941165 ≤ 215973933)
    (by decide : 215973933 ≤ 216006701) block2 block3

theorem join_1_0 : (twinPrimeSegment 215875629 216006701).card = 454 := by
  simpa using combineTwinPrimeSegments (by decide : 215875629 ≤ 215941165)
    (by decide : 215941165 ≤ 216006701) join_0_0 join_0_1

theorem total : (twinPrimeSegment 215875629 216006701).card = 454 := join_1_0

end S102C15
end Sude.GeneratedTwinScan
