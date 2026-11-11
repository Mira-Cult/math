import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B28 (S112..S115). -/
namespace Sude.FastTwinScan
namespace B28
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 234881069 236978221 = 7573 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 234881069 236978221).card = 7573 := by
  have h := fastStrideSixIntervalScan_spec 234881069 236978221 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 236978221 239075373 = 7520 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 236978221 239075373).card = 7520 := by
  have h := fastStrideSixIntervalScan_spec 236978221 239075373 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 239075373 241172525 = 7492 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 239075373 241172525).card = 7492 := by
  have h := fastStrideSixIntervalScan_spec 239075373 241172525 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 241172525 243269677 = 7425 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 241172525 243269677).card = 7425 := by
  have h := fastStrideSixIntervalScan_spec 241172525 243269677 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 234881069 239075373).card = 15093 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 236978221) (by decide : 236978221 ≤ 239075373) seg0 seg1

theorem join23 : (twinPrimeSegment 239075373 243269677).card = 14917 := by
  simpa using combineTwinPrimeSegments (by decide : 239075373 ≤ 241172525) (by decide : 241172525 ≤ 243269677) seg2 seg3

theorem total : (twinPrimeSegment 234881069 243269677).card = 30010 := by
  simpa using combineTwinPrimeSegments (by decide : 234881069 ≤ 239075373) (by decide : 239075373 ≤ 243269677) join01 join23

end
end B28
end Sude.FastTwinScan
