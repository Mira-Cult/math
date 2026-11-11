import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B37 (S148..S151). -/
namespace Sude.FastTwinScan
namespace B37
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 310378541 312475693 = 7291 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 310378541 312475693).card = 7291 := by
  have h := fastStrideSixIntervalScan_spec 310378541 312475693 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 312475693 314572845 = 7165 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 312475693 314572845).card = 7165 := by
  have h := fastStrideSixIntervalScan_spec 312475693 314572845 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 314572845 316669997 = 7140 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 314572845 316669997).card = 7140 := by
  have h := fastStrideSixIntervalScan_spec 314572845 316669997 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 316669997 318767149 = 7319 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 316669997 318767149).card = 7319 := by
  have h := fastStrideSixIntervalScan_spec 316669997 318767149 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 310378541 314572845).card = 14456 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 312475693) (by decide : 312475693 ≤ 314572845) seg0 seg1

theorem join23 : (twinPrimeSegment 314572845 318767149).card = 14459 := by
  simpa using combineTwinPrimeSegments (by decide : 314572845 ≤ 316669997) (by decide : 316669997 ≤ 318767149) seg2 seg3

theorem total : (twinPrimeSegment 310378541 318767149).card = 28915 := by
  simpa using combineTwinPrimeSegments (by decide : 310378541 ≤ 314572845) (by decide : 314572845 ≤ 318767149) join01 join23

end
end B37
end Sude.FastTwinScan
