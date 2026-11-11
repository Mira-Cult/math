import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B51 (S204..S207). -/
namespace Sude.FastTwinScan
namespace B51
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 427819053 429916205 = 6949 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 427819053 429916205).card = 6949 := by
  have h := fastStrideSixIntervalScan_spec 427819053 429916205 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 429916205 432013357 = 6981 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 429916205 432013357).card = 6981 := by
  have h := fastStrideSixIntervalScan_spec 429916205 432013357 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 432013357 434110509 = 7007 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 432013357 434110509).card = 7007 := by
  have h := fastStrideSixIntervalScan_spec 432013357 434110509 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 434110509 436207661 = 7095 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 434110509 436207661).card = 7095 := by
  have h := fastStrideSixIntervalScan_spec 434110509 436207661 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 427819053 432013357).card = 13930 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 429916205) (by decide : 429916205 ≤ 432013357) seg0 seg1

theorem join23 : (twinPrimeSegment 432013357 436207661).card = 14102 := by
  simpa using combineTwinPrimeSegments (by decide : 432013357 ≤ 434110509) (by decide : 434110509 ≤ 436207661) seg2 seg3

theorem total : (twinPrimeSegment 427819053 436207661).card = 28032 := by
  simpa using combineTwinPrimeSegments (by decide : 427819053 ≤ 432013357) (by decide : 432013357 ≤ 436207661) join01 join23

end
end B51
end Sude.FastTwinScan
