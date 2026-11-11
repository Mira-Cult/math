import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B107 (S428..S431). -/
namespace Sude.FastTwinScan
namespace B107
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 897581101 899678253 = 6589 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 897581101 899678253).card = 6589 := by
  have h := fastStrideSixIntervalScan_spec 897581101 899678253 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 899678253 901775405 = 6591 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 899678253 901775405).card = 6591 := by
  have h := fastStrideSixIntervalScan_spec 899678253 901775405 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 901775405 903872557 = 6467 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 901775405 903872557).card = 6467 := by
  have h := fastStrideSixIntervalScan_spec 901775405 903872557 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 903872557 905969709 = 6536 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 903872557 905969709).card = 6536 := by
  have h := fastStrideSixIntervalScan_spec 903872557 905969709 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 897581101 901775405).card = 13180 := by
  simpa using combineTwinPrimeSegments (by decide : 897581101 ≤ 899678253) (by decide : 899678253 ≤ 901775405) seg0 seg1

theorem join23 : (twinPrimeSegment 901775405 905969709).card = 13003 := by
  simpa using combineTwinPrimeSegments (by decide : 901775405 ≤ 903872557) (by decide : 903872557 ≤ 905969709) seg2 seg3

theorem total : (twinPrimeSegment 897581101 905969709).card = 26183 := by
  simpa using combineTwinPrimeSegments (by decide : 897581101 ≤ 901775405) (by decide : 901775405 ≤ 905969709) join01 join23

end
end B107
end Sude.FastTwinScan
