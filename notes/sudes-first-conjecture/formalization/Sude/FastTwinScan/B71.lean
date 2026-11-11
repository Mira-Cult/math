import Sude.FastTwinStrideSixScan
import Sude.FiniteTwinFlexible

/-! Fast single-pass stride-six twin-prime certificate for segment block B71 (S284..S287). -/
namespace Sude.FastTwinScan
namespace B71
noncomputable section

set_option autoImplicit false
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem check0 : fastStrideSixIntervalScan 595591213 597688365 = 6787 := by
  decide +kernel

theorem seg0 : (twinPrimeSegment 595591213 597688365).card = 6787 := by
  have h := fastStrideSixIntervalScan_spec 595591213 597688365 (by decide) (by decide) (by decide)
  rw [check0] at h
  exact h.symm

theorem check1 : fastStrideSixIntervalScan 597688365 599785517 = 6769 := by
  decide +kernel

theorem seg1 : (twinPrimeSegment 597688365 599785517).card = 6769 := by
  have h := fastStrideSixIntervalScan_spec 597688365 599785517 (by decide) (by decide) (by decide)
  rw [check1] at h
  exact h.symm

theorem check2 : fastStrideSixIntervalScan 599785517 601882669 = 6773 := by
  decide +kernel

theorem seg2 : (twinPrimeSegment 599785517 601882669).card = 6773 := by
  have h := fastStrideSixIntervalScan_spec 599785517 601882669 (by decide) (by decide) (by decide)
  rw [check2] at h
  exact h.symm

theorem check3 : fastStrideSixIntervalScan 601882669 603979821 = 6880 := by
  decide +kernel

theorem seg3 : (twinPrimeSegment 601882669 603979821).card = 6880 := by
  have h := fastStrideSixIntervalScan_spec 601882669 603979821 (by decide) (by decide) (by decide)
  rw [check3] at h
  exact h.symm

theorem join01 : (twinPrimeSegment 595591213 599785517).card = 13556 := by
  simpa using combineTwinPrimeSegments (by decide : 595591213 ≤ 597688365) (by decide : 597688365 ≤ 599785517) seg0 seg1

theorem join23 : (twinPrimeSegment 599785517 603979821).card = 13653 := by
  simpa using combineTwinPrimeSegments (by decide : 599785517 ≤ 601882669) (by decide : 601882669 ≤ 603979821) seg2 seg3

theorem total : (twinPrimeSegment 595591213 603979821).card = 27209 := by
  simpa using combineTwinPrimeSegments (by decide : 595591213 ≤ 599785517) (by decide : 599785517 ≤ 603979821) join01 join23

end
end B71
end Sude.FastTwinScan
