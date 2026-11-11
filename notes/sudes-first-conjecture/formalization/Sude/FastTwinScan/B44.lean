import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B44 (S176..S179). -/
namespace Sude.FastTwinScan
namespace B44
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 369098797 371195949 = 7120 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 369098797 371195949).card = 7120 := by
  have h := fastStrideSixIntervalScan_spec 369098797 371195949 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 371195949 373293101 = 7136 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 371195949 373293101).card = 7136 := by
  have h := fastStrideSixIntervalScan_spec 371195949 373293101 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 373293101 375390253 = 7130 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 373293101 375390253).card = 7130 := by
  have h := fastStrideSixIntervalScan_spec 373293101 375390253 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 375390253 377487405 = 7079 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 375390253 377487405).card = 7079 := by
  have h := fastStrideSixIntervalScan_spec 375390253 377487405 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 369098797 373293101).card = 14256 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 371195949) (by decide : 371195949 ≤ 373293101) seg0 seg1

theorem join23 : (twinPrimeSegment 373293101 377487405).card = 14209 := by
  simpa using combineTwinPrimeSegments (by decide : 373293101 ≤ 375390253) (by decide : 375390253 ≤ 377487405) seg2 seg3

theorem total : (twinPrimeSegment 369098797 377487405).card = 28465 := by
  simpa using combineTwinPrimeSegments (by decide : 369098797 ≤ 373293101) (by decide : 373293101 ≤ 377487405) join01 join23

end
end B44
end Sude.FastTwinScan
