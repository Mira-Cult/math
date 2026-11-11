import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B43 (S172..S175). -/
namespace Sude.FastTwinScan
namespace B43
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 360710189 362807341 = 7093 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 360710189 362807341).card = 7093 := by
  have h := fastStrideSixIntervalScan_spec 360710189 362807341 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 362807341 364904493 = 7257 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 362807341 364904493).card = 7257 := by
  have h := fastStrideSixIntervalScan_spec 362807341 364904493 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 364904493 367001645 = 7092 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 364904493 367001645).card = 7092 := by
  have h := fastStrideSixIntervalScan_spec 364904493 367001645 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 367001645 369098797 = 7049 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 367001645 369098797).card = 7049 := by
  have h := fastStrideSixIntervalScan_spec 367001645 369098797 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 360710189 364904493).card = 14350 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 362807341) (by decide : 362807341 ≤ 364904493) seg0 seg1

theorem join23 : (twinPrimeSegment 364904493 369098797).card = 14141 := by
  simpa using combineTwinPrimeSegments (by decide : 364904493 ≤ 367001645) (by decide : 367001645 ≤ 369098797) seg2 seg3

theorem total : (twinPrimeSegment 360710189 369098797).card = 28491 := by
  simpa using combineTwinPrimeSegments (by decide : 360710189 ≤ 364904493) (by decide : 364904493 ≤ 369098797) join01 join23

end
end B43
end Sude.FastTwinScan
