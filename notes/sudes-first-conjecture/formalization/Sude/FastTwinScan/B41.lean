import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B41 (S164..S167). -/
namespace Sude.FastTwinScan
namespace B41
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 343932973 346030125 = 7226 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 343932973 346030125).card = 7226 := by
  have h := fastStrideSixIntervalScan_spec 343932973 346030125 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 346030125 348127277 = 7128 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 346030125 348127277).card = 7128 := by
  have h := fastStrideSixIntervalScan_spec 346030125 348127277 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 348127277 350224429 = 7122 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 348127277 350224429).card = 7122 := by
  have h := fastStrideSixIntervalScan_spec 348127277 350224429 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 350224429 352321581 = 7040 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 350224429 352321581).card = 7040 := by
  have h := fastStrideSixIntervalScan_spec 350224429 352321581 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 343932973 348127277).card = 14354 := by
  simpa using combineTwinPrimeSegments (by decide : 343932973 ≤ 346030125) (by decide : 346030125 ≤ 348127277) seg0 seg1

theorem join23 : (twinPrimeSegment 348127277 352321581).card = 14162 := by
  simpa using combineTwinPrimeSegments (by decide : 348127277 ≤ 350224429) (by decide : 350224429 ≤ 352321581) seg2 seg3

theorem total : (twinPrimeSegment 343932973 352321581).card = 28516 := by
  simpa using combineTwinPrimeSegments (by decide : 343932973 ≤ 348127277) (by decide : 348127277 ≤ 352321581) join01 join23

end
end B41
end Sude.FastTwinScan
