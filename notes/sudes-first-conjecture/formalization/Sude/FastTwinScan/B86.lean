import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B86 (S344..S347). -/
namespace Sude.FastTwinScan
namespace B86
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 721420333 723517485 = 6600 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 721420333 723517485).card = 6600 := by
  have h := fastStrideSixIntervalScan_spec 721420333 723517485 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 723517485 725614637 = 6767 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 723517485 725614637).card = 6767 := by
  have h := fastStrideSixIntervalScan_spec 723517485 725614637 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 725614637 727711789 = 6715 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 725614637 727711789).card = 6715 := by
  have h := fastStrideSixIntervalScan_spec 725614637 727711789 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 727711789 729808941 = 6606 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 727711789 729808941).card = 6606 := by
  have h := fastStrideSixIntervalScan_spec 727711789 729808941 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 721420333 725614637).card = 13367 := by
  simpa using combineTwinPrimeSegments (by decide : 721420333 ≤ 723517485) (by decide : 723517485 ≤ 725614637) seg0 seg1

theorem join23 : (twinPrimeSegment 725614637 729808941).card = 13321 := by
  simpa using combineTwinPrimeSegments (by decide : 725614637 ≤ 727711789) (by decide : 727711789 ≤ 729808941) seg2 seg3

theorem total : (twinPrimeSegment 721420333 729808941).card = 26688 := by
  simpa using combineTwinPrimeSegments (by decide : 721420333 ≤ 725614637) (by decide : 725614637 ≤ 729808941) join01 join23

end
end B86
end Sude.FastTwinScan
