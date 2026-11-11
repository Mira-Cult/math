import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B21 (S084..S087). -/
namespace Sude.FastTwinScan
namespace B21
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 176160813 178257965 = 7680 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 176160813 178257965).card = 7680 := by
  have h := fastStrideSixIntervalScan_spec 176160813 178257965 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 178257965 180355117 = 7651 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 178257965 180355117).card = 7651 := by
  have h := fastStrideSixIntervalScan_spec 178257965 180355117 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 180355117 182452269 = 7542 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 180355117 182452269).card = 7542 := by
  have h := fastStrideSixIntervalScan_spec 180355117 182452269 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 182452269 184549421 = 7600 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 182452269 184549421).card = 7600 := by
  have h := fastStrideSixIntervalScan_spec 182452269 184549421 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 176160813 180355117).card = 15331 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 178257965) (by decide : 178257965 ≤ 180355117) seg0 seg1

theorem join23 : (twinPrimeSegment 180355117 184549421).card = 15142 := by
  simpa using combineTwinPrimeSegments (by decide : 180355117 ≤ 182452269) (by decide : 182452269 ≤ 184549421) seg2 seg3

theorem total : (twinPrimeSegment 176160813 184549421).card = 30473 := by
  simpa using combineTwinPrimeSegments (by decide : 176160813 ≤ 180355117) (by decide : 180355117 ≤ 184549421) join01 join23

end
end B21
end Sude.FastTwinScan
