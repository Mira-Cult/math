import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B109 (S436..S439). -/
namespace Sude.FastTwinScan
namespace B109
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 914358317 916455469 = 6573 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 914358317 916455469).card = 6573 := by
  have h := fastStrideSixIntervalScan_spec 914358317 916455469 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 916455469 918552621 = 6434 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 916455469 918552621).card = 6434 := by
  have h := fastStrideSixIntervalScan_spec 916455469 918552621 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 918552621 920649773 = 6456 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 918552621 920649773).card = 6456 := by
  have h := fastStrideSixIntervalScan_spec 918552621 920649773 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 920649773 922746925 = 6514 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 920649773 922746925).card = 6514 := by
  have h := fastStrideSixIntervalScan_spec 920649773 922746925 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 914358317 918552621).card = 13007 := by
  simpa using combineTwinPrimeSegments (by decide : 914358317 ≤ 916455469) (by decide : 916455469 ≤ 918552621) seg0 seg1

theorem join23 : (twinPrimeSegment 918552621 922746925).card = 12970 := by
  simpa using combineTwinPrimeSegments (by decide : 918552621 ≤ 920649773) (by decide : 920649773 ≤ 922746925) seg2 seg3

theorem total : (twinPrimeSegment 914358317 922746925).card = 25977 := by
  simpa using combineTwinPrimeSegments (by decide : 914358317 ≤ 918552621) (by decide : 918552621 ≤ 922746925) join01 join23

end
end B109
end Sude.FastTwinScan
