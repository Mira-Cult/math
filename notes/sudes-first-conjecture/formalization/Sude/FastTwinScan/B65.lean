import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B65 (S260..S263). -/
namespace Sude.FastTwinScan
namespace B65
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 545259565 547356717 = 6877 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 545259565 547356717).card = 6877 := by
  have h := fastStrideSixIntervalScan_spec 545259565 547356717 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 547356717 549453869 = 6879 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 547356717 549453869).card = 6879 := by
  have h := fastStrideSixIntervalScan_spec 547356717 549453869 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 549453869 551551021 = 6920 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 549453869 551551021).card = 6920 := by
  have h := fastStrideSixIntervalScan_spec 549453869 551551021 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 551551021 553648173 = 6747 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 551551021 553648173).card = 6747 := by
  have h := fastStrideSixIntervalScan_spec 551551021 553648173 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 545259565 549453869).card = 13756 := by
  simpa using combineTwinPrimeSegments (by decide : 545259565 ≤ 547356717) (by decide : 547356717 ≤ 549453869) seg0 seg1

theorem join23 : (twinPrimeSegment 549453869 553648173).card = 13667 := by
  simpa using combineTwinPrimeSegments (by decide : 549453869 ≤ 551551021) (by decide : 551551021 ≤ 553648173) seg2 seg3

theorem total : (twinPrimeSegment 545259565 553648173).card = 27423 := by
  simpa using combineTwinPrimeSegments (by decide : 545259565 ≤ 549453869) (by decide : 549453869 ≤ 553648173) join01 join23

end
end B65
end Sude.FastTwinScan
