import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B118 (S472..S475). -/
namespace Sude.FastTwinScan
namespace B118
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 989855789 991952941 = 6381 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 989855789 991952941).card = 6381 := by
  have h := fastStrideSixIntervalScan_spec 989855789 991952941 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 991952941 994050093 = 6436 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 991952941 994050093).card = 6436 := by
  have h := fastStrideSixIntervalScan_spec 991952941 994050093 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 994050093 996147245 = 6482 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 994050093 996147245).card = 6482 := by
  have h := fastStrideSixIntervalScan_spec 994050093 996147245 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 996147245 998244397 = 6430 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 996147245 998244397).card = 6430 := by
  have h := fastStrideSixIntervalScan_spec 996147245 998244397 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 989855789 994050093).card = 12817 := by
  simpa using combineTwinPrimeSegments (by decide : 989855789 ≤ 991952941) (by decide : 991952941 ≤ 994050093) seg0 seg1

theorem join23 : (twinPrimeSegment 994050093 998244397).card = 12912 := by
  simpa using combineTwinPrimeSegments (by decide : 994050093 ≤ 996147245) (by decide : 996147245 ≤ 998244397) seg2 seg3

theorem total : (twinPrimeSegment 989855789 998244397).card = 25729 := by
  simpa using combineTwinPrimeSegments (by decide : 989855789 ≤ 994050093) (by decide : 994050093 ≤ 998244397) join01 join23

end
end B118
end Sude.FastTwinScan
