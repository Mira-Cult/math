import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B114 (S456..S459). -/
namespace Sude.FastTwinScan
namespace B114
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 956301357 958398509 = 6505 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 956301357 958398509).card = 6505 := by
  have h := fastStrideSixIntervalScan_spec 956301357 958398509 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 958398509 960495661 = 6405 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 958398509 960495661).card = 6405 := by
  have h := fastStrideSixIntervalScan_spec 958398509 960495661 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 960495661 962592813 = 6412 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 960495661 962592813).card = 6412 := by
  have h := fastStrideSixIntervalScan_spec 960495661 962592813 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 962592813 964689965 = 6520 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 962592813 964689965).card = 6520 := by
  have h := fastStrideSixIntervalScan_spec 962592813 964689965 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 956301357 960495661).card = 12910 := by
  simpa using combineTwinPrimeSegments (by decide : 956301357 ≤ 958398509) (by decide : 958398509 ≤ 960495661) seg0 seg1

theorem join23 : (twinPrimeSegment 960495661 964689965).card = 12932 := by
  simpa using combineTwinPrimeSegments (by decide : 960495661 ≤ 962592813) (by decide : 962592813 ≤ 964689965) seg2 seg3

theorem total : (twinPrimeSegment 956301357 964689965).card = 25842 := by
  simpa using combineTwinPrimeSegments (by decide : 956301357 ≤ 960495661) (by decide : 960495661 ≤ 964689965) join01 join23

end
end B114
end Sude.FastTwinScan
