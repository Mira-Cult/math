import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B09 (S036..S039). -/
namespace Sude.FastTwinScan
namespace B09
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 75497517 77594669 = 8433 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 75497517 77594669).card = 8433 := by
  have h := fastStrideSixIntervalScan_spec 75497517 77594669 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 77594669 79691821 = 8316 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 77594669 79691821).card = 8316 := by
  have h := fastStrideSixIntervalScan_spec 77594669 79691821 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 79691821 81788973 = 8359 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 79691821 81788973).card = 8359 := by
  have h := fastStrideSixIntervalScan_spec 79691821 81788973 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 81788973 83886125 = 8317 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 81788973 83886125).card = 8317 := by
  have h := fastStrideSixIntervalScan_spec 81788973 83886125 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 75497517 79691821).card = 16749 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 77594669) (by decide : 77594669 ≤ 79691821) seg0 seg1

theorem join23 : (twinPrimeSegment 79691821 83886125).card = 16676 := by
  simpa using combineTwinPrimeSegments (by decide : 79691821 ≤ 81788973) (by decide : 81788973 ≤ 83886125) seg2 seg3

theorem total : (twinPrimeSegment 75497517 83886125).card = 33425 := by
  simpa using combineTwinPrimeSegments (by decide : 75497517 ≤ 79691821) (by decide : 79691821 ≤ 83886125) join01 join23

end
end B09
end Sude.FastTwinScan
