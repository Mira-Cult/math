import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B50 (S200..S203). -/
namespace Sude.FastTwinScan
namespace B50
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 419430445 421527597 = 7131 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 419430445 421527597).card = 7131 := by
  have h := fastStrideSixIntervalScan_spec 419430445 421527597 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 421527597 423624749 = 7041 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 421527597 423624749).card = 7041 := by
  have h := fastStrideSixIntervalScan_spec 421527597 423624749 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 423624749 425721901 = 6991 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 423624749 425721901).card = 6991 := by
  have h := fastStrideSixIntervalScan_spec 423624749 425721901 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 425721901 427819053 = 6968 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 425721901 427819053).card = 6968 := by
  have h := fastStrideSixIntervalScan_spec 425721901 427819053 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 419430445 423624749).card = 14172 := by
  simpa using combineTwinPrimeSegments (by decide : 419430445 ≤ 421527597) (by decide : 421527597 ≤ 423624749) seg0 seg1

theorem join23 : (twinPrimeSegment 423624749 427819053).card = 13959 := by
  simpa using combineTwinPrimeSegments (by decide : 423624749 ≤ 425721901) (by decide : 425721901 ≤ 427819053) seg2 seg3

theorem total : (twinPrimeSegment 419430445 427819053).card = 28131 := by
  simpa using combineTwinPrimeSegments (by decide : 419430445 ≤ 423624749) (by decide : 423624749 ≤ 427819053) join01 join23

end
end B50
end Sude.FastTwinScan
