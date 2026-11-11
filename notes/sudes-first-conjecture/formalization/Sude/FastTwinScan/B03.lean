import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B03 (S012..S015). -/
namespace Sude.FastTwinScan
namespace B03
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 25165869 27263021 = 9458 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 25165869 27263021).card = 9458 := by
  have h := fastStrideSixIntervalScan_spec 25165869 27263021 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 27263021 29360173 = 9342 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 27263021 29360173).card = 9342 := by
  have h := fastStrideSixIntervalScan_spec 27263021 29360173 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 29360173 31457325 = 9334 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 29360173 31457325).card = 9334 := by
  have h := fastStrideSixIntervalScan_spec 29360173 31457325 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 31457325 33554477 = 9230 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 31457325 33554477).card = 9230 := by
  have h := fastStrideSixIntervalScan_spec 31457325 33554477 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 25165869 29360173).card = 18800 := by
  simpa using combineTwinPrimeSegments (by decide : 25165869 ≤ 27263021) (by decide : 27263021 ≤ 29360173) seg0 seg1

theorem join23 : (twinPrimeSegment 29360173 33554477).card = 18564 := by
  simpa using combineTwinPrimeSegments (by decide : 29360173 ≤ 31457325) (by decide : 31457325 ≤ 33554477) seg2 seg3

theorem total : (twinPrimeSegment 25165869 33554477).card = 37364 := by
  simpa using combineTwinPrimeSegments (by decide : 25165869 ≤ 29360173) (by decide : 29360173 ≤ 33554477) join01 join23

end
end B03
end Sude.FastTwinScan
