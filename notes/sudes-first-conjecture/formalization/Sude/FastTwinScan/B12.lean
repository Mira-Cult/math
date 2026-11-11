import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B12 (S048..S051). -/
namespace Sude.FastTwinScan
namespace B12
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 100663341 102760493 = 8029 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 100663341 102760493).card = 8029 := by
  have h := fastStrideSixIntervalScan_spec 100663341 102760493 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 102760493 104857645 = 8224 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 102760493 104857645).card = 8224 := by
  have h := fastStrideSixIntervalScan_spec 102760493 104857645 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 104857645 106954797 = 8203 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 104857645 106954797).card = 8203 := by
  have h := fastStrideSixIntervalScan_spec 104857645 106954797 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 106954797 109051949 = 8112 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 106954797 109051949).card = 8112 := by
  have h := fastStrideSixIntervalScan_spec 106954797 109051949 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 100663341 104857645).card = 16253 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 102760493) (by decide : 102760493 ≤ 104857645) seg0 seg1

theorem join23 : (twinPrimeSegment 104857645 109051949).card = 16315 := by
  simpa using combineTwinPrimeSegments (by decide : 104857645 ≤ 106954797) (by decide : 106954797 ≤ 109051949) seg2 seg3

theorem total : (twinPrimeSegment 100663341 109051949).card = 32568 := by
  simpa using combineTwinPrimeSegments (by decide : 100663341 ≤ 104857645) (by decide : 104857645 ≤ 109051949) join01 join23

end
end B12
end Sude.FastTwinScan
