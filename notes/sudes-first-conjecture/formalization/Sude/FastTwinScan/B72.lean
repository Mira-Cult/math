import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B72 (S288..S291). -/
namespace Sude.FastTwinScan
namespace B72
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 603979821 606076973 = 6723 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 603979821 606076973).card = 6723 := by
  have h := fastStrideSixIntervalScan_spec 603979821 606076973 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 606076973 608174125 = 6668 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 606076973 608174125).card = 6668 := by
  have h := fastStrideSixIntervalScan_spec 606076973 608174125 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 608174125 610271277 = 6768 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 608174125 610271277).card = 6768 := by
  have h := fastStrideSixIntervalScan_spec 608174125 610271277 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 610271277 612368429 = 6837 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 610271277 612368429).card = 6837 := by
  have h := fastStrideSixIntervalScan_spec 610271277 612368429 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 603979821 608174125).card = 13391 := by
  simpa using combineTwinPrimeSegments (by decide : 603979821 ≤ 606076973) (by decide : 606076973 ≤ 608174125) seg0 seg1

theorem join23 : (twinPrimeSegment 608174125 612368429).card = 13605 := by
  simpa using combineTwinPrimeSegments (by decide : 608174125 ≤ 610271277) (by decide : 610271277 ≤ 612368429) seg2 seg3

theorem total : (twinPrimeSegment 603979821 612368429).card = 26996 := by
  simpa using combineTwinPrimeSegments (by decide : 603979821 ≤ 608174125) (by decide : 608174125 ≤ 612368429) join01 join23

end
end B72
end Sude.FastTwinScan
