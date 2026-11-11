import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B103 (S412..S415). -/
namespace Sude.FastTwinScan
namespace B103
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 864026669 866123821 = 6605 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 864026669 866123821).card = 6605 := by
  have h := fastStrideSixIntervalScan_spec 864026669 866123821 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 866123821 868220973 = 6446 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 866123821 868220973).card = 6446 := by
  have h := fastStrideSixIntervalScan_spec 866123821 868220973 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 868220973 870318125 = 6543 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 868220973 870318125).card = 6543 := by
  have h := fastStrideSixIntervalScan_spec 868220973 870318125 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 870318125 872415277 = 6518 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 870318125 872415277).card = 6518 := by
  have h := fastStrideSixIntervalScan_spec 870318125 872415277 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 864026669 868220973).card = 13051 := by
  simpa using combineTwinPrimeSegments (by decide : 864026669 ≤ 866123821) (by decide : 866123821 ≤ 868220973) seg0 seg1

theorem join23 : (twinPrimeSegment 868220973 872415277).card = 13061 := by
  simpa using combineTwinPrimeSegments (by decide : 868220973 ≤ 870318125) (by decide : 870318125 ≤ 872415277) seg2 seg3

theorem total : (twinPrimeSegment 864026669 872415277).card = 26112 := by
  simpa using combineTwinPrimeSegments (by decide : 864026669 ≤ 868220973) (by decide : 868220973 ≤ 872415277) join01 join23

end
end B103
end Sude.FastTwinScan
