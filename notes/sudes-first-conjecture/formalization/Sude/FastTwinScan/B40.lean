import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B40 (S160..S163). -/
namespace Sude.FastTwinScan
namespace B40
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 335544365 337641517 = 7206 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 335544365 337641517).card = 7206 := by
  have h := fastStrideSixIntervalScan_spec 335544365 337641517 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 337641517 339738669 = 7105 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 337641517 339738669).card = 7105 := by
  have h := fastStrideSixIntervalScan_spec 337641517 339738669 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 339738669 341835821 = 7152 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 339738669 341835821).card = 7152 := by
  have h := fastStrideSixIntervalScan_spec 339738669 341835821 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 341835821 343932973 = 7204 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 341835821 343932973).card = 7204 := by
  have h := fastStrideSixIntervalScan_spec 341835821 343932973 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 335544365 339738669).card = 14311 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 337641517) (by decide : 337641517 ≤ 339738669) seg0 seg1

theorem join23 : (twinPrimeSegment 339738669 343932973).card = 14356 := by
  simpa using combineTwinPrimeSegments (by decide : 339738669 ≤ 341835821) (by decide : 341835821 ≤ 343932973) seg2 seg3

theorem total : (twinPrimeSegment 335544365 343932973).card = 28667 := by
  simpa using combineTwinPrimeSegments (by decide : 335544365 ≤ 339738669) (by decide : 339738669 ≤ 343932973) join01 join23

end
end B40
end Sude.FastTwinScan
