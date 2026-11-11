import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B10 (S040..S043). -/
namespace Sude.FastTwinScan
namespace B10
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 83886125 85983277 = 8299 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 83886125 85983277).card = 8299 := by
  have h := fastStrideSixIntervalScan_spec 83886125 85983277 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 85983277 88080429 = 8335 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 85983277 88080429).card = 8335 := by
  have h := fastStrideSixIntervalScan_spec 85983277 88080429 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 88080429 90177581 = 8239 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 88080429 90177581).card = 8239 := by
  have h := fastStrideSixIntervalScan_spec 88080429 90177581 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 90177581 92274733 = 8325 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 90177581 92274733).card = 8325 := by
  have h := fastStrideSixIntervalScan_spec 90177581 92274733 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 83886125 88080429).card = 16634 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 85983277) (by decide : 85983277 ≤ 88080429) seg0 seg1

theorem join23 : (twinPrimeSegment 88080429 92274733).card = 16564 := by
  simpa using combineTwinPrimeSegments (by decide : 88080429 ≤ 90177581) (by decide : 90177581 ≤ 92274733) seg2 seg3

theorem total : (twinPrimeSegment 83886125 92274733).card = 33198 := by
  simpa using combineTwinPrimeSegments (by decide : 83886125 ≤ 88080429) (by decide : 88080429 ≤ 92274733) join01 join23

end
end B10
end Sude.FastTwinScan
