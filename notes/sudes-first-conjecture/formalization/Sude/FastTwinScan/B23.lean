import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B23 (S092..S095). -/
namespace Sude.FastTwinScan
namespace B23
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 192938029 195035181 = 7663 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 192938029 195035181).card = 7663 := by
  have h := fastStrideSixIntervalScan_spec 192938029 195035181 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 195035181 197132333 = 7561 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 195035181 197132333).card = 7561 := by
  have h := fastStrideSixIntervalScan_spec 195035181 197132333 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 197132333 199229485 = 7611 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 197132333 199229485).card = 7611 := by
  have h := fastStrideSixIntervalScan_spec 197132333 199229485 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 199229485 201326637 = 7683 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 199229485 201326637).card = 7683 := by
  have h := fastStrideSixIntervalScan_spec 199229485 201326637 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 192938029 197132333).card = 15224 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 195035181) (by decide : 195035181 ≤ 197132333) seg0 seg1

theorem join23 : (twinPrimeSegment 197132333 201326637).card = 15294 := by
  simpa using combineTwinPrimeSegments (by decide : 197132333 ≤ 199229485) (by decide : 199229485 ≤ 201326637) seg2 seg3

theorem total : (twinPrimeSegment 192938029 201326637).card = 30518 := by
  simpa using combineTwinPrimeSegments (by decide : 192938029 ≤ 197132333) (by decide : 197132333 ≤ 201326637) join01 join23

end
end B23
end Sude.FastTwinScan
