import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B00 (S000..S003). -/
namespace Sude.FastTwinScan
namespace B00
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 45 2097197 = 15494 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 45 2097197).card = 15494 := by
  have h := fastStrideSixIntervalScan_spec 45 2097197 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 2097197 4194349 = 12495 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 2097197 4194349).card = 12495 := by
  have h := fastStrideSixIntervalScan_spec 2097197 4194349 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 4194349 6291501 = 11535 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 4194349 6291501).card = 11535 := by
  have h := fastStrideSixIntervalScan_spec 4194349 6291501 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 6291501 8388653 = 11109 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 6291501 8388653).card = 11109 := by
  have h := fastStrideSixIntervalScan_spec 6291501 8388653 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 45 4194349).card = 27989 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 2097197) (by decide : 2097197 ≤ 4194349) seg0 seg1

theorem join23 : (twinPrimeSegment 4194349 8388653).card = 22644 := by
  simpa using combineTwinPrimeSegments (by decide : 4194349 ≤ 6291501) (by decide : 6291501 ≤ 8388653) seg2 seg3

theorem total : (twinPrimeSegment 45 8388653).card = 50633 := by
  simpa using combineTwinPrimeSegments (by decide : 45 ≤ 4194349) (by decide : 4194349 ≤ 8388653) join01 join23

end
end B00
end Sude.FastTwinScan
