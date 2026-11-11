import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B60 (S240..S243). -/
namespace Sude.FastTwinScan
namespace B60
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 503316525 505413677 = 6876 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 503316525 505413677).card = 6876 := by
  have h := fastStrideSixIntervalScan_spec 503316525 505413677 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 505413677 507510829 = 6882 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 505413677 507510829).card = 6882 := by
  have h := fastStrideSixIntervalScan_spec 505413677 507510829 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 507510829 509607981 = 7008 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 507510829 509607981).card = 7008 := by
  have h := fastStrideSixIntervalScan_spec 507510829 509607981 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 509607981 511705133 = 6789 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 509607981 511705133).card = 6789 := by
  have h := fastStrideSixIntervalScan_spec 509607981 511705133 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 503316525 507510829).card = 13758 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 505413677) (by decide : 505413677 ≤ 507510829) seg0 seg1

theorem join23 : (twinPrimeSegment 507510829 511705133).card = 13797 := by
  simpa using combineTwinPrimeSegments (by decide : 507510829 ≤ 509607981) (by decide : 509607981 ≤ 511705133) seg2 seg3

theorem total : (twinPrimeSegment 503316525 511705133).card = 27555 := by
  simpa using combineTwinPrimeSegments (by decide : 503316525 ≤ 507510829) (by decide : 507510829 ≤ 511705133) join01 join23

end
end B60
end Sude.FastTwinScan
