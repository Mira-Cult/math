import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B34 (S136..S139). -/
namespace Sude.FastTwinScan
namespace B34
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 285212717 287309869 = 7366 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 285212717 287309869).card = 7366 := by
  have h := fastStrideSixIntervalScan_spec 285212717 287309869 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 287309869 289407021 = 7383 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 287309869 289407021).card = 7383 := by
  have h := fastStrideSixIntervalScan_spec 287309869 289407021 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 289407021 291504173 = 7306 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 289407021 291504173).card = 7306 := by
  have h := fastStrideSixIntervalScan_spec 289407021 291504173 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 291504173 293601325 = 7338 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 291504173 293601325).card = 7338 := by
  have h := fastStrideSixIntervalScan_spec 291504173 293601325 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 285212717 289407021).card = 14749 := by
  simpa using combineTwinPrimeSegments (by decide : 285212717 ≤ 287309869) (by decide : 287309869 ≤ 289407021) seg0 seg1

theorem join23 : (twinPrimeSegment 289407021 293601325).card = 14644 := by
  simpa using combineTwinPrimeSegments (by decide : 289407021 ≤ 291504173) (by decide : 291504173 ≤ 293601325) seg2 seg3

theorem total : (twinPrimeSegment 285212717 293601325).card = 29393 := by
  simpa using combineTwinPrimeSegments (by decide : 285212717 ≤ 289407021) (by decide : 289407021 ≤ 293601325) join01 join23

end
end B34
end Sude.FastTwinScan
