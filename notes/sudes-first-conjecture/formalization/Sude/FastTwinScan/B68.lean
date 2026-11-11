import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B68 (S272..S275). -/
namespace Sude.FastTwinScan
namespace B68
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 570425389 572522541 = 6685 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 570425389 572522541).card = 6685 := by
  have h := fastStrideSixIntervalScan_spec 570425389 572522541 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 572522541 574619693 = 6785 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 572522541 574619693).card = 6785 := by
  have h := fastStrideSixIntervalScan_spec 572522541 574619693 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 574619693 576716845 = 6816 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 574619693 576716845).card = 6816 := by
  have h := fastStrideSixIntervalScan_spec 574619693 576716845 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 576716845 578813997 = 6890 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 576716845 578813997).card = 6890 := by
  have h := fastStrideSixIntervalScan_spec 576716845 578813997 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 570425389 574619693).card = 13470 := by
  simpa using combineTwinPrimeSegments (by decide : 570425389 ≤ 572522541) (by decide : 572522541 ≤ 574619693) seg0 seg1

theorem join23 : (twinPrimeSegment 574619693 578813997).card = 13706 := by
  simpa using combineTwinPrimeSegments (by decide : 574619693 ≤ 576716845) (by decide : 576716845 ≤ 578813997) seg2 seg3

theorem total : (twinPrimeSegment 570425389 578813997).card = 27176 := by
  simpa using combineTwinPrimeSegments (by decide : 570425389 ≤ 574619693) (by decide : 574619693 ≤ 578813997) join01 join23

end
end B68
end Sude.FastTwinScan
