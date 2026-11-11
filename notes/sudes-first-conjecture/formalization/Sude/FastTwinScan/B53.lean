import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B53 (S212..S215). -/
namespace Sude.FastTwinScan
namespace B53
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 444596269 446693421 = 7019 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 444596269 446693421).card = 7019 := by
  have h := fastStrideSixIntervalScan_spec 444596269 446693421 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 446693421 448790573 = 6962 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 446693421 448790573).card = 6962 := by
  have h := fastStrideSixIntervalScan_spec 446693421 448790573 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 448790573 450887725 = 6991 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 448790573 450887725).card = 6991 := by
  have h := fastStrideSixIntervalScan_spec 448790573 450887725 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 450887725 452984877 = 6920 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 450887725 452984877).card = 6920 := by
  have h := fastStrideSixIntervalScan_spec 450887725 452984877 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 444596269 448790573).card = 13981 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 446693421) (by decide : 446693421 ≤ 448790573) seg0 seg1

theorem join23 : (twinPrimeSegment 448790573 452984877).card = 13911 := by
  simpa using combineTwinPrimeSegments (by decide : 448790573 ≤ 450887725) (by decide : 450887725 ≤ 452984877) seg2 seg3

theorem total : (twinPrimeSegment 444596269 452984877).card = 27892 := by
  simpa using combineTwinPrimeSegments (by decide : 444596269 ≤ 448790573) (by decide : 448790573 ≤ 452984877) join01 join23

end
end B53
end Sude.FastTwinScan
