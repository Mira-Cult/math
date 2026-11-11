import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B52 (S208..S211). -/
namespace Sude.FastTwinScan
namespace B52
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 436207661 438304813 = 7068 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 436207661 438304813).card = 7068 := by
  have h := fastStrideSixIntervalScan_spec 436207661 438304813 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 438304813 440401965 = 7038 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 438304813 440401965).card = 7038 := by
  have h := fastStrideSixIntervalScan_spec 438304813 440401965 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 440401965 442499117 = 6964 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 440401965 442499117).card = 6964 := by
  have h := fastStrideSixIntervalScan_spec 440401965 442499117 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 442499117 444596269 = 6983 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 442499117 444596269).card = 6983 := by
  have h := fastStrideSixIntervalScan_spec 442499117 444596269 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 436207661 440401965).card = 14106 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 438304813) (by decide : 438304813 ≤ 440401965) seg0 seg1

theorem join23 : (twinPrimeSegment 440401965 444596269).card = 13947 := by
  simpa using combineTwinPrimeSegments (by decide : 440401965 ≤ 442499117) (by decide : 442499117 ≤ 444596269) seg2 seg3

theorem total : (twinPrimeSegment 436207661 444596269).card = 28053 := by
  simpa using combineTwinPrimeSegments (by decide : 436207661 ≤ 440401965) (by decide : 440401965 ≤ 444596269) join01 join23

end
end B52
end Sude.FastTwinScan
