import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B126 (S504..S507). -/
namespace Sude.FastTwinScan
namespace B126
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 1056964653 1059061805 = 6385 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 1056964653 1059061805).card = 6385 := by
  have h := fastStrideSixIntervalScan_spec 1056964653 1059061805 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 1059061805 1061158957 = 6470 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 1059061805 1061158957).card = 6470 := by
  have h := fastStrideSixIntervalScan_spec 1059061805 1061158957 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 1061158957 1063256109 = 6437 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 1061158957 1063256109).card = 6437 := by
  have h := fastStrideSixIntervalScan_spec 1061158957 1063256109 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 1063256109 1065353261 = 6438 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 1063256109 1065353261).card = 6438 := by
  have h := fastStrideSixIntervalScan_spec 1063256109 1065353261 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 1056964653 1061158957).card = 12855 := by
  simpa using combineTwinPrimeSegments (by decide : 1056964653 ≤ 1059061805) (by decide : 1059061805 ≤ 1061158957) seg0 seg1

theorem join23 : (twinPrimeSegment 1061158957 1065353261).card = 12875 := by
  simpa using combineTwinPrimeSegments (by decide : 1061158957 ≤ 1063256109) (by decide : 1063256109 ≤ 1065353261) seg2 seg3

theorem total : (twinPrimeSegment 1056964653 1065353261).card = 25730 := by
  simpa using combineTwinPrimeSegments (by decide : 1056964653 ≤ 1061158957) (by decide : 1061158957 ≤ 1065353261) join01 join23

end
end B126
end Sude.FastTwinScan
