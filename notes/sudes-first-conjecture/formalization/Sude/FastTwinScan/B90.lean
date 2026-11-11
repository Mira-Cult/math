import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B90 (S360..S363). -/
namespace Sude.FastTwinScan
namespace B90
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 754974765 757071917 = 6703 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 754974765 757071917).card = 6703 := by
  have h := fastStrideSixIntervalScan_spec 754974765 757071917 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 757071917 759169069 = 6619 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 757071917 759169069).card = 6619 := by
  have h := fastStrideSixIntervalScan_spec 757071917 759169069 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 759169069 761266221 = 6478 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 759169069 761266221).card = 6478 := by
  have h := fastStrideSixIntervalScan_spec 759169069 761266221 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 761266221 763363373 = 6569 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 761266221 763363373).card = 6569 := by
  have h := fastStrideSixIntervalScan_spec 761266221 763363373 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 754974765 759169069).card = 13322 := by
  simpa using combineTwinPrimeSegments (by decide : 754974765 ≤ 757071917) (by decide : 757071917 ≤ 759169069) seg0 seg1

theorem join23 : (twinPrimeSegment 759169069 763363373).card = 13047 := by
  simpa using combineTwinPrimeSegments (by decide : 759169069 ≤ 761266221) (by decide : 761266221 ≤ 763363373) seg2 seg3

theorem total : (twinPrimeSegment 754974765 763363373).card = 26369 := by
  simpa using combineTwinPrimeSegments (by decide : 754974765 ≤ 759169069) (by decide : 759169069 ≤ 763363373) join01 join23

end
end B90
end Sude.FastTwinScan
