import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B38 (S152..S155). -/
namespace Sude.FastTwinScan
namespace B38
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 318767149 320864301 = 7299 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 318767149 320864301).card = 7299 := by
  have h := fastStrideSixIntervalScan_spec 318767149 320864301 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 320864301 322961453 = 7190 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 320864301 322961453).card = 7190 := by
  have h := fastStrideSixIntervalScan_spec 320864301 322961453 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 322961453 325058605 = 7322 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 322961453 325058605).card = 7322 := by
  have h := fastStrideSixIntervalScan_spec 322961453 325058605 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 325058605 327155757 = 7224 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 325058605 327155757).card = 7224 := by
  have h := fastStrideSixIntervalScan_spec 325058605 327155757 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 318767149 322961453).card = 14489 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 320864301) (by decide : 320864301 ≤ 322961453) seg0 seg1

theorem join23 : (twinPrimeSegment 322961453 327155757).card = 14546 := by
  simpa using combineTwinPrimeSegments (by decide : 322961453 ≤ 325058605) (by decide : 325058605 ≤ 327155757) seg2 seg3

theorem total : (twinPrimeSegment 318767149 327155757).card = 29035 := by
  simpa using combineTwinPrimeSegments (by decide : 318767149 ≤ 322961453) (by decide : 322961453 ≤ 327155757) join01 join23

end
end B38
end Sude.FastTwinScan
