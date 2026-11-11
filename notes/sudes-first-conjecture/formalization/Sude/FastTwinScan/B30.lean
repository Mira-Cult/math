import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B30 (S120..S123). -/
namespace Sude.FastTwinScan
namespace B30
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 251658285 253755437 = 7413 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 251658285 253755437).card = 7413 := by
  have h := fastStrideSixIntervalScan_spec 251658285 253755437 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 253755437 255852589 = 7498 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 253755437 255852589).card = 7498 := by
  have h := fastStrideSixIntervalScan_spec 253755437 255852589 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 255852589 257949741 = 7219 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 255852589 257949741).card = 7219 := by
  have h := fastStrideSixIntervalScan_spec 255852589 257949741 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 257949741 260046893 = 7329 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 257949741 260046893).card = 7329 := by
  have h := fastStrideSixIntervalScan_spec 257949741 260046893 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 251658285 255852589).card = 14911 := by
  simpa using combineTwinPrimeSegments (by decide : 251658285 ≤ 253755437) (by decide : 253755437 ≤ 255852589) seg0 seg1

theorem join23 : (twinPrimeSegment 255852589 260046893).card = 14548 := by
  simpa using combineTwinPrimeSegments (by decide : 255852589 ≤ 257949741) (by decide : 257949741 ≤ 260046893) seg2 seg3

theorem total : (twinPrimeSegment 251658285 260046893).card = 29459 := by
  simpa using combineTwinPrimeSegments (by decide : 251658285 ≤ 255852589) (by decide : 255852589 ≤ 260046893) join01 join23

end
end B30
end Sude.FastTwinScan
