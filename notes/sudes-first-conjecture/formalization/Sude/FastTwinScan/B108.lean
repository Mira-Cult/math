import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B108 (S432..S435). -/
namespace Sude.FastTwinScan
namespace B108
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 905969709 908066861 = 6480 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 905969709 908066861).card = 6480 := by
  have h := fastStrideSixIntervalScan_spec 905969709 908066861 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 908066861 910164013 = 6626 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 908066861 910164013).card = 6626 := by
  have h := fastStrideSixIntervalScan_spec 908066861 910164013 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 910164013 912261165 = 6516 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 910164013 912261165).card = 6516 := by
  have h := fastStrideSixIntervalScan_spec 910164013 912261165 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 912261165 914358317 = 6537 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 912261165 914358317).card = 6537 := by
  have h := fastStrideSixIntervalScan_spec 912261165 914358317 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 905969709 910164013).card = 13106 := by
  simpa using combineTwinPrimeSegments (by decide : 905969709 ≤ 908066861) (by decide : 908066861 ≤ 910164013) seg0 seg1

theorem join23 : (twinPrimeSegment 910164013 914358317).card = 13053 := by
  simpa using combineTwinPrimeSegments (by decide : 910164013 ≤ 912261165) (by decide : 912261165 ≤ 914358317) seg2 seg3

theorem total : (twinPrimeSegment 905969709 914358317).card = 26159 := by
  simpa using combineTwinPrimeSegments (by decide : 905969709 ≤ 910164013) (by decide : 910164013 ≤ 914358317) join01 join23

end
end B108
end Sude.FastTwinScan
