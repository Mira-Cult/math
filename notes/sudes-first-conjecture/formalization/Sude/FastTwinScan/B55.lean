import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B55 (S220..S223). -/
namespace Sude.FastTwinScan
namespace B55
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 461373485 463470637 = 6904 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 461373485 463470637).card = 6904 := by
  have h := fastStrideSixIntervalScan_spec 461373485 463470637 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 463470637 465567789 = 6854 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 463470637 465567789).card = 6854 := by
  have h := fastStrideSixIntervalScan_spec 463470637 465567789 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 465567789 467664941 = 7053 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 465567789 467664941).card = 7053 := by
  have h := fastStrideSixIntervalScan_spec 465567789 467664941 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 467664941 469762093 = 6826 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 467664941 469762093).card = 6826 := by
  have h := fastStrideSixIntervalScan_spec 467664941 469762093 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 461373485 465567789).card = 13758 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 463470637) (by decide : 463470637 ≤ 465567789) seg0 seg1

theorem join23 : (twinPrimeSegment 465567789 469762093).card = 13879 := by
  simpa using combineTwinPrimeSegments (by decide : 465567789 ≤ 467664941) (by decide : 467664941 ≤ 469762093) seg2 seg3

theorem total : (twinPrimeSegment 461373485 469762093).card = 27637 := by
  simpa using combineTwinPrimeSegments (by decide : 461373485 ≤ 465567789) (by decide : 465567789 ≤ 469762093) join01 join23

end
end B55
end Sude.FastTwinScan
