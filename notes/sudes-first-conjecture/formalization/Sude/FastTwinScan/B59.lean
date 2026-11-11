import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B59 (S236..S239). -/
namespace Sude.FastTwinScan
namespace B59
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 494927917 497025069 = 6902 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 494927917 497025069).card = 6902 := by
  have h := fastStrideSixIntervalScan_spec 494927917 497025069 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 497025069 499122221 = 6880 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 497025069 499122221).card = 6880 := by
  have h := fastStrideSixIntervalScan_spec 497025069 499122221 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 499122221 501219373 = 6895 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 499122221 501219373).card = 6895 := by
  have h := fastStrideSixIntervalScan_spec 499122221 501219373 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 501219373 503316525 = 6819 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 501219373 503316525).card = 6819 := by
  have h := fastStrideSixIntervalScan_spec 501219373 503316525 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 494927917 499122221).card = 13782 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 497025069) (by decide : 497025069 ≤ 499122221) seg0 seg1

theorem join23 : (twinPrimeSegment 499122221 503316525).card = 13714 := by
  simpa using combineTwinPrimeSegments (by decide : 499122221 ≤ 501219373) (by decide : 501219373 ≤ 503316525) seg2 seg3

theorem total : (twinPrimeSegment 494927917 503316525).card = 27496 := by
  simpa using combineTwinPrimeSegments (by decide : 494927917 ≤ 499122221) (by decide : 499122221 ≤ 503316525) join01 join23

end
end B59
end Sude.FastTwinScan
