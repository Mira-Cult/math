import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B67 (S268..S271). -/
namespace Sude.FastTwinScan
namespace B67
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 562036781 564133933 = 6802 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 562036781 564133933).card = 6802 := by
  have h := fastStrideSixIntervalScan_spec 562036781 564133933 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 564133933 566231085 = 6896 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 564133933 566231085).card = 6896 := by
  have h := fastStrideSixIntervalScan_spec 564133933 566231085 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 566231085 568328237 = 6772 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 566231085 568328237).card = 6772 := by
  have h := fastStrideSixIntervalScan_spec 566231085 568328237 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 568328237 570425389 = 6851 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 568328237 570425389).card = 6851 := by
  have h := fastStrideSixIntervalScan_spec 568328237 570425389 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 562036781 566231085).card = 13698 := by
  simpa using combineTwinPrimeSegments (by decide : 562036781 ≤ 564133933) (by decide : 564133933 ≤ 566231085) seg0 seg1

theorem join23 : (twinPrimeSegment 566231085 570425389).card = 13623 := by
  simpa using combineTwinPrimeSegments (by decide : 566231085 ≤ 568328237) (by decide : 568328237 ≤ 570425389) seg2 seg3

theorem total : (twinPrimeSegment 562036781 570425389).card = 27321 := by
  simpa using combineTwinPrimeSegments (by decide : 562036781 ≤ 566231085) (by decide : 566231085 ≤ 570425389) join01 join23

end
end B67
end Sude.FastTwinScan
