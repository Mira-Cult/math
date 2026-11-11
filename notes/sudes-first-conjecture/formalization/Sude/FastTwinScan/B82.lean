import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B82 (S328..S331). -/
namespace Sude.FastTwinScan
namespace B82
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 687865901 689963053 = 6755 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 687865901 689963053).card = 6755 := by
  have h := fastStrideSixIntervalScan_spec 687865901 689963053 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 689963053 692060205 = 6644 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 689963053 692060205).card = 6644 := by
  have h := fastStrideSixIntervalScan_spec 689963053 692060205 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 692060205 694157357 = 6680 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 692060205 694157357).card = 6680 := by
  have h := fastStrideSixIntervalScan_spec 692060205 694157357 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 694157357 696254509 = 6661 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 694157357 696254509).card = 6661 := by
  have h := fastStrideSixIntervalScan_spec 694157357 696254509 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 687865901 692060205).card = 13399 := by
  simpa using combineTwinPrimeSegments (by decide : 687865901 ≤ 689963053) (by decide : 689963053 ≤ 692060205) seg0 seg1

theorem join23 : (twinPrimeSegment 692060205 696254509).card = 13341 := by
  simpa using combineTwinPrimeSegments (by decide : 692060205 ≤ 694157357) (by decide : 694157357 ≤ 696254509) seg2 seg3

theorem total : (twinPrimeSegment 687865901 696254509).card = 26740 := by
  simpa using combineTwinPrimeSegments (by decide : 687865901 ≤ 692060205) (by decide : 692060205 ≤ 696254509) join01 join23

end
end B82
end Sude.FastTwinScan
