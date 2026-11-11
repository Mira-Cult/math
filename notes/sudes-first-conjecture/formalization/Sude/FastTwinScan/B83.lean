import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B83 (S332..S335). -/
namespace Sude.FastTwinScan
namespace B83
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 696254509 698351661 = 6543 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 696254509 698351661).card = 6543 := by
  have h := fastStrideSixIntervalScan_spec 696254509 698351661 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 698351661 700448813 = 6718 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 698351661 700448813).card = 6718 := by
  have h := fastStrideSixIntervalScan_spec 698351661 700448813 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 700448813 702545965 = 6678 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 700448813 702545965).card = 6678 := by
  have h := fastStrideSixIntervalScan_spec 700448813 702545965 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 702545965 704643117 = 6676 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 702545965 704643117).card = 6676 := by
  have h := fastStrideSixIntervalScan_spec 702545965 704643117 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 696254509 700448813).card = 13261 := by
  simpa using combineTwinPrimeSegments (by decide : 696254509 ≤ 698351661) (by decide : 698351661 ≤ 700448813) seg0 seg1

theorem join23 : (twinPrimeSegment 700448813 704643117).card = 13354 := by
  simpa using combineTwinPrimeSegments (by decide : 700448813 ≤ 702545965) (by decide : 702545965 ≤ 704643117) seg2 seg3

theorem total : (twinPrimeSegment 696254509 704643117).card = 26615 := by
  simpa using combineTwinPrimeSegments (by decide : 696254509 ≤ 700448813) (by decide : 700448813 ≤ 704643117) join01 join23

end
end B83
end Sude.FastTwinScan
