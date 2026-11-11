import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S226C02
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21777)) 474218541 474251309 = 91 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 474218541 474251309).card = 91 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21777 474218541 474251309
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21778)) 474251309 474284077 = 105 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 474251309 474284077).card = 105 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21778 474251309 474284077
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21778)) 474284077 474316845 = 113 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 474284077 474316845).card = 113 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21778 474284077 474316845
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 21779)) 474316845 474349613 = 100 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 474316845 474349613).card = 100 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 21779 474316845 474349613
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 474218541 474284077).card = 196 := by
  simpa using combineTwinPrimeSegments (by decide : 474218541 ≤ 474251309)
    (by decide : 474251309 ≤ 474284077) block0 block1

theorem join_0_1 : (twinPrimeSegment 474284077 474349613).card = 213 := by
  simpa using combineTwinPrimeSegments (by decide : 474284077 ≤ 474316845)
    (by decide : 474316845 ≤ 474349613) block2 block3

theorem join_1_0 : (twinPrimeSegment 474218541 474349613).card = 409 := by
  simpa using combineTwinPrimeSegments (by decide : 474218541 ≤ 474284077)
    (by decide : 474284077 ≤ 474349613) join_0_0 join_0_1

theorem total : (twinPrimeSegment 474218541 474349613).card = 409 := join_1_0

end S226C02
end Sude.GeneratedTwinScan
