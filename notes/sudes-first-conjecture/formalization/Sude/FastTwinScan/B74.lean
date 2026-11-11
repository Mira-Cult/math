import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B74 (S296..S299). -/
namespace Sude.FastTwinScan
namespace B74
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 620757037 622854189 = 6745 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 620757037 622854189).card = 6745 := by
  have h := fastStrideSixIntervalScan_spec 620757037 622854189 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 622854189 624951341 = 6677 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 622854189 624951341).card = 6677 := by
  have h := fastStrideSixIntervalScan_spec 622854189 624951341 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 624951341 627048493 = 6735 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 624951341 627048493).card = 6735 := by
  have h := fastStrideSixIntervalScan_spec 624951341 627048493 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 627048493 629145645 = 6834 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 627048493 629145645).card = 6834 := by
  have h := fastStrideSixIntervalScan_spec 627048493 629145645 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 620757037 624951341).card = 13422 := by
  simpa using combineTwinPrimeSegments (by decide : 620757037 ≤ 622854189) (by decide : 622854189 ≤ 624951341) seg0 seg1

theorem join23 : (twinPrimeSegment 624951341 629145645).card = 13569 := by
  simpa using combineTwinPrimeSegments (by decide : 624951341 ≤ 627048493) (by decide : 627048493 ≤ 629145645) seg2 seg3

theorem total : (twinPrimeSegment 620757037 629145645).card = 26991 := by
  simpa using combineTwinPrimeSegments (by decide : 620757037 ≤ 624951341) (by decide : 624951341 ≤ 629145645) join01 join23

end
end B74
end Sude.FastTwinScan
