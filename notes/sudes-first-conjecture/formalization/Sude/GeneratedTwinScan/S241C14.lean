import Sude.FiniteTwinTakeWhileBase
import Sude.FiniteTwinActive

/-! Generated FT hints; Lean checks each prefix scan and lookahead. -/
namespace Sude.GeneratedTwinScan
namespace S241C14
set_option maxRecDepth 100000
set_option maxHeartbeats 0

theorem checked0 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22522)) 507248685 507281453 = 107 := by
  decide +kernel

theorem block0 : (twinPrimeSegment 507248685 507281453).card = 107 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22522 507248685 507281453
    (by decide) (by decide) (by decide)
  rw [checked0] at h
  exact h.symm

theorem checked1 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22523)) 507281453 507314221 = 109 := by
  decide +kernel

theorem block1 : (twinPrimeSegment 507281453 507314221).card = 109 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22523 507281453 507314221
    (by decide) (by decide) (by decide)
  rw [checked1] at h
  exact h.symm

theorem checked2 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22524)) 507314221 507346989 = 117 := by
  decide +kernel

theorem block2 : (twinPrimeSegment 507314221 507346989).card = 117 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22524 507314221 507346989
    (by decide) (by decide) (by decide)
  rw [checked2] at h
  exact h.symm

theorem checked3 : strideSixCompressedIntervalScan (finiteTwinCheckedBase.takeWhile (fun p => p ≤ 22525)) 507346989 507379757 = 116 := by
  decide +kernel

theorem block3 : (twinPrimeSegment 507346989 507379757).card = 116 := by
  have h := finiteTwinTakeWhile_compressed_interval_spec 22525 507346989 507379757
    (by decide) (by decide) (by decide)
  rw [checked3] at h
  exact h.symm

theorem join_0_0 : (twinPrimeSegment 507248685 507314221).card = 216 := by
  simpa using combineTwinPrimeSegments (by decide : 507248685 ≤ 507281453)
    (by decide : 507281453 ≤ 507314221) block0 block1

theorem join_0_1 : (twinPrimeSegment 507314221 507379757).card = 233 := by
  simpa using combineTwinPrimeSegments (by decide : 507314221 ≤ 507346989)
    (by decide : 507346989 ≤ 507379757) block2 block3

theorem join_1_0 : (twinPrimeSegment 507248685 507379757).card = 449 := by
  simpa using combineTwinPrimeSegments (by decide : 507248685 ≤ 507314221)
    (by decide : 507314221 ≤ 507379757) join_0_0 join_0_1

theorem total : (twinPrimeSegment 507248685 507379757).card = 449 := join_1_0

end S241C14
end Sude.GeneratedTwinScan
